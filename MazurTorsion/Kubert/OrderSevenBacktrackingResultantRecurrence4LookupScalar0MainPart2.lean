/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_1
  recurrence4B0_coeff_10
  recurrence4B0_coeff_100
  recurrence4B0_coeff_101
  recurrence4B0_coeff_102
  recurrence4B0_coeff_103
  recurrence4B0_coeff_104
  recurrence4B0_coeff_105
  recurrence4B0_coeff_106
  recurrence4B0_coeff_107
  recurrence4B0_coeff_108
  recurrence4B0_coeff_109
  recurrence4B0_coeff_11
  recurrence4B0_coeff_110
  recurrence4B0_coeff_111
  recurrence4B0_coeff_112
  recurrence4B0_coeff_113
  recurrence4B0_coeff_114
  recurrence4B0_coeff_115
  recurrence4B0_coeff_116
  recurrence4B0_coeff_117
  recurrence4B0_coeff_118
  recurrence4B0_coeff_119
  recurrence4B0_coeff_12
  recurrence4B0_coeff_120
  recurrence4B0_coeff_121
  recurrence4B0_coeff_122
  recurrence4B0_coeff_123
  recurrence4B0_coeff_124
  recurrence4B0_coeff_125
  recurrence4B0_coeff_126
  recurrence4B0_coeff_127
  recurrence4B0_coeff_128
  recurrence4B0_coeff_129
  recurrence4B0_coeff_13
  recurrence4B0_coeff_130
  recurrence4B0_coeff_131
  recurrence4B0_coeff_132
  recurrence4B0_coeff_133
  recurrence4B0_coeff_134
  recurrence4B0_coeff_135
  recurrence4B0_coeff_136
  recurrence4B0_coeff_137
  recurrence4B0_coeff_138
  recurrence4B0_coeff_139
  recurrence4B0_coeff_14
  recurrence4B0_coeff_140
  recurrence4B0_coeff_141
  recurrence4B0_coeff_142
  recurrence4B0_coeff_143
  recurrence4B0_coeff_144
  recurrence4B0_coeff_145
  recurrence4B0_coeff_146
  recurrence4B0_coeff_147
  recurrence4B0_coeff_148
  recurrence4B0_coeff_149
  recurrence4B0_coeff_15
  recurrence4B0_coeff_150
  recurrence4B0_coeff_151
  recurrence4B0_coeff_152
  recurrence4B0_coeff_153
  recurrence4B0_coeff_154
  recurrence4B0_coeff_155
  recurrence4B0_coeff_156

attribute [local simp]
  recurrence4B0_coeff_157
  recurrence4B0_coeff_158
  recurrence4B0_coeff_159
  recurrence4B0_coeff_16
  recurrence4B0_coeff_160
  recurrence4B0_coeff_161
  recurrence4B0_coeff_162
  recurrence4B0_coeff_163
  recurrence4B0_coeff_164
  recurrence4B0_coeff_165
  recurrence4B0_coeff_166
  recurrence4B0_coeff_167
  recurrence4B0_coeff_168
  recurrence4B0_coeff_169
  recurrence4B0_coeff_17
  recurrence4B0_coeff_170
  recurrence4B0_coeff_171
  recurrence4B0_coeff_172
  recurrence4B0_coeff_173
  recurrence4B0_coeff_174
  recurrence4B0_coeff_175
  recurrence4B0_coeff_176
  recurrence4B0_coeff_18
  recurrence4B0_coeff_19
  recurrence4B0_coeff_2
  recurrence4B0_coeff_20
  recurrence4B0_coeff_21
  recurrence4B0_coeff_22
  recurrence4B0_coeff_23
  recurrence4B0_coeff_24
  recurrence4B0_coeff_25
  recurrence4B0_coeff_26
  recurrence4B0_coeff_27
  recurrence4B0_coeff_28
  recurrence4B0_coeff_29
  recurrence4B0_coeff_3
  recurrence4B0_coeff_30
  recurrence4B0_coeff_31
  recurrence4B0_coeff_32
  recurrence4B0_coeff_33
  recurrence4B0_coeff_34
  recurrence4B0_coeff_35
  recurrence4B0_coeff_36
  recurrence4B0_coeff_37
  recurrence4B0_coeff_38
  recurrence4B0_coeff_39
  recurrence4B0_coeff_4
  recurrence4B0_coeff_40
  recurrence4B0_coeff_41
  recurrence4B0_coeff_42
  recurrence4B0_coeff_43
  recurrence4B0_coeff_44
  recurrence4B0_coeff_45
  recurrence4B0_coeff_46
  recurrence4B0_coeff_47
  recurrence4B0_coeff_48
  recurrence4B0_coeff_49
  recurrence4B0_coeff_5
  recurrence4B0_coeff_50
  recurrence4B0_coeff_51
  recurrence4B0_coeff_52
  recurrence4B0_coeff_53
  recurrence4B0_coeff_54
  recurrence4B0_coeff_55

attribute [local simp]
  recurrence4B0_coeff_56
  recurrence4B0_coeff_57
  recurrence4B0_coeff_58
  recurrence4B0_coeff_59
  recurrence4B0_coeff_6
  recurrence4B0_coeff_60
  recurrence4B0_coeff_61
  recurrence4B0_coeff_62
  recurrence4B0_coeff_63
  recurrence4B0_coeff_64
  recurrence4B0_coeff_65
  recurrence4B0_coeff_66
  recurrence4B0_coeff_67
  recurrence4B0_coeff_68
  recurrence4B0_coeff_69
  recurrence4B0_coeff_7
  recurrence4B0_coeff_70
  recurrence4B0_coeff_71
  recurrence4B0_coeff_72
  recurrence4B0_coeff_73
  recurrence4B0_coeff_74
  recurrence4B0_coeff_75
  recurrence4B0_coeff_76
  recurrence4B0_coeff_77
  recurrence4B0_coeff_78
  recurrence4B0_coeff_79
  recurrence4B0_coeff_8
  recurrence4B0_coeff_80
  recurrence4B0_coeff_81
  recurrence4B0_coeff_82
  recurrence4B0_coeff_83
  recurrence4B0_coeff_84
  recurrence4B0_coeff_85
  recurrence4B0_coeff_86
  recurrence4B0_coeff_87
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_9
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
  recurrence4QuotientConstant_coeff_101
  recurrence4QuotientConstant_coeff_102
  recurrence4QuotientConstant_coeff_103
  recurrence4QuotientConstant_coeff_104
  recurrence4QuotientConstant_coeff_105
  recurrence4QuotientConstant_coeff_106
  recurrence4QuotientConstant_coeff_107
  recurrence4QuotientConstant_coeff_108
  recurrence4QuotientConstant_coeff_109
  recurrence4QuotientConstant_coeff_110
  recurrence4QuotientConstant_coeff_111
  recurrence4QuotientConstant_coeff_112
  recurrence4QuotientConstant_coeff_113
  recurrence4QuotientConstant_coeff_114
  recurrence4QuotientConstant_coeff_115
  recurrence4QuotientConstant_coeff_116

attribute [local simp]
  recurrence4QuotientConstant_coeff_117
  recurrence4QuotientConstant_coeff_118
  recurrence4QuotientConstant_coeff_119
  recurrence4QuotientConstant_coeff_120
  recurrence4QuotientConstant_coeff_121
  recurrence4QuotientConstant_coeff_122
  recurrence4QuotientConstant_coeff_123
  recurrence4QuotientConstant_coeff_124
  recurrence4QuotientConstant_coeff_125
  recurrence4QuotientConstant_coeff_126
  recurrence4QuotientConstant_coeff_127
  recurrence4QuotientConstant_coeff_128
  recurrence4QuotientConstant_coeff_129
  recurrence4QuotientConstant_coeff_130
  recurrence4QuotientConstant_coeff_131
  recurrence4QuotientConstant_coeff_132
  recurrence4QuotientConstant_coeff_133
  recurrence4QuotientConstant_coeff_134
  recurrence4QuotientConstant_coeff_135
  recurrence4QuotientConstant_coeff_136
  recurrence4QuotientConstant_coeff_137
  recurrence4QuotientConstant_coeff_138
  recurrence4QuotientConstant_coeff_139
  recurrence4QuotientConstant_coeff_140
  recurrence4QuotientConstant_coeff_141
  recurrence4QuotientConstant_coeff_142
  recurrence4QuotientConstant_coeff_143
  recurrence4QuotientConstant_coeff_144
  recurrence4QuotientConstant_coeff_145
  recurrence4QuotientConstant_coeff_146
  recurrence4QuotientConstant_coeff_147
  recurrence4QuotientConstant_coeff_148
  recurrence4QuotientConstant_coeff_149
  recurrence4QuotientConstant_coeff_150
  recurrence4QuotientConstant_coeff_151
  recurrence4QuotientConstant_coeff_152
  recurrence4QuotientConstant_coeff_153
  recurrence4QuotientConstant_coeff_154
  recurrence4QuotientConstant_coeff_155
  recurrence4QuotientConstant_coeff_156
  recurrence4QuotientConstant_coeff_157
  recurrence4QuotientConstant_coeff_158
  recurrence4QuotientConstant_coeff_159
  recurrence4QuotientConstant_coeff_160
  recurrence4QuotientConstant_coeff_161
  recurrence4QuotientConstant_coeff_162
  recurrence4QuotientConstant_coeff_163
  recurrence4QuotientConstant_coeff_164
  recurrence4QuotientConstant_coeff_165
  recurrence4QuotientConstant_coeff_166
  recurrence4QuotientConstant_coeff_167
  recurrence4QuotientConstant_coeff_168
  recurrence4QuotientConstant_coeff_169
  recurrence4QuotientConstant_coeff_170
  recurrence4QuotientConstant_coeff_171
  recurrence4QuotientConstant_coeff_172
  recurrence4QuotientConstant_coeff_173
  recurrence4QuotientConstant_coeff_174
  recurrence4QuotientConstant_coeff_175
  recurrence4QuotientConstant_coeff_176
  recurrence4QuotientConstant_coeff_177
  recurrence4QuotientConstant_coeff_178
  recurrence4QuotientConstant_coeff_179
  recurrence4QuotientConstant_coeff_180

attribute [local simp]
  recurrence4QuotientConstant_coeff_181
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186
  recurrence4QuotientConstant_coeff_187
  recurrence4QuotientConstant_coeff_188
  recurrence4QuotientConstant_coeff_189
  recurrence4QuotientConstant_coeff_190
  recurrence4QuotientConstant_coeff_191
  recurrence4QuotientConstant_coeff_192
  recurrence4QuotientConstant_coeff_193
  recurrence4QuotientConstant_coeff_194
  recurrence4QuotientConstant_coeff_195
  recurrence4QuotientConstant_coeff_196
  recurrence4QuotientConstant_coeff_197
  recurrence4QuotientConstant_coeff_198
  recurrence4QuotientConstant_coeff_199
  recurrence4QuotientConstant_coeff_200
  recurrence4QuotientConstant_coeff_201
  recurrence4QuotientConstant_coeff_202
  recurrence4QuotientConstant_coeff_203
  recurrence4QuotientConstant_coeff_204
  recurrence4QuotientConstant_coeff_205
  recurrence4QuotientConstant_coeff_206
  recurrence4QuotientConstant_coeff_207
  recurrence4QuotientConstant_coeff_208
  recurrence4QuotientConstant_coeff_209
  recurrence4QuotientConstant_coeff_210
  recurrence4QuotientConstant_coeff_211
  recurrence4QuotientConstant_coeff_212
  recurrence4QuotientConstant_coeff_213
  recurrence4QuotientConstant_coeff_214
  recurrence4QuotientConstant_coeff_215
  recurrence4QuotientConstant_coeff_216
  recurrence4QuotientConstant_coeff_217
  recurrence4QuotientConstant_coeff_218
  recurrence4QuotientConstant_coeff_219
  recurrence4QuotientConstant_coeff_220
  recurrence4QuotientConstant_coeff_221
  recurrence4QuotientConstant_coeff_222
  recurrence4QuotientConstant_coeff_223
  recurrence4QuotientConstant_coeff_224
  recurrence4QuotientConstant_coeff_225
  recurrence4QuotientConstant_coeff_226
  recurrence4QuotientConstant_coeff_227
  recurrence4QuotientConstant_coeff_228
  recurrence4QuotientConstant_coeff_229
  recurrence4QuotientConstant_coeff_230
  recurrence4QuotientConstant_coeff_231
  recurrence4QuotientConstant_coeff_232
  recurrence4QuotientConstant_coeff_233
  recurrence4QuotientConstant_coeff_234
  recurrence4QuotientConstant_coeff_235
  recurrence4QuotientConstant_coeff_236
  recurrence4QuotientConstant_coeff_237
  recurrence4QuotientConstant_coeff_238
  recurrence4QuotientConstant_coeff_239
  recurrence4QuotientConstant_coeff_240
  recurrence4QuotientConstant_coeff_241
  recurrence4QuotientConstant_coeff_242
  recurrence4QuotientConstant_coeff_243
  recurrence4QuotientConstant_coeff_244

attribute [local simp]
  recurrence4QuotientConstant_coeff_245
  recurrence4QuotientConstant_coeff_246
  recurrence4QuotientConstant_coeff_247
  recurrence4QuotientConstant_coeff_248
  recurrence4QuotientConstant_coeff_249
  recurrence4QuotientConstant_coeff_250
  recurrence4QuotientConstant_coeff_251
  recurrence4QuotientConstant_coeff_252
  recurrence4QuotientConstant_coeff_253
  recurrence4QuotientConstant_coeff_254
  recurrence4QuotientConstant_coeff_255
  recurrence4QuotientConstant_coeff_256
  recurrence4QuotientConstant_coeff_257
  recurrence4QuotientConstant_coeff_258
  recurrence4QuotientConstant_coeff_259
  recurrence4QuotientConstant_coeff_260
  recurrence4QuotientConstant_coeff_261
  recurrence4QuotientConstant_coeff_262
  recurrence4QuotientConstant_coeff_263
  recurrence4QuotientConstant_coeff_264
  recurrence4QuotientConstant_coeff_265
  recurrence4QuotientConstant_coeff_266
  recurrence4QuotientConstant_coeff_267
  recurrence4QuotientConstant_coeff_268
  recurrence4QuotientConstant_coeff_269
  recurrence4QuotientConstant_coeff_270
  recurrence4QuotientConstant_coeff_271
  recurrence4QuotientConstant_coeff_272
  recurrence4QuotientConstant_coeff_273
  recurrence4QuotientConstant_coeff_274
  recurrence4QuotientConstant_coeff_275
  recurrence4QuotientConstant_coeff_276
  recurrence4QuotientConstant_coeff_277
  recurrence4QuotientConstant_coeff_278
  recurrence4QuotientConstant_coeff_279
  recurrence4QuotientConstant_coeff_280
  recurrence4QuotientConstant_coeff_281
  recurrence4QuotientConstant_coeff_282
  recurrence4QuotientConstant_coeff_283
  recurrence4QuotientConstant_coeff_284
  recurrence4QuotientConstant_coeff_285
  recurrence4QuotientConstant_coeff_286
  recurrence4QuotientConstant_coeff_287
  recurrence4QuotientConstant_coeff_288
  recurrence4QuotientConstant_coeff_289
  recurrence4QuotientConstant_coeff_290
  recurrence4QuotientConstant_coeff_291
  recurrence4QuotientConstant_coeff_292
  recurrence4QuotientConstant_coeff_293
  recurrence4QuotientConstant_coeff_294
  recurrence4QuotientConstant_coeff_295
  recurrence4QuotientConstant_coeff_296
  recurrence4QuotientConstant_coeff_297
  recurrence4QuotientConstant_coeff_298
  recurrence4QuotientConstant_coeff_299
  recurrence4QuotientConstant_coeff_300
  recurrence4QuotientConstant_coeff_301
  recurrence4QuotientConstant_coeff_302
  recurrence4QuotientConstant_coeff_303
  recurrence4QuotientConstant_coeff_304
  recurrence4QuotientConstant_coeff_305
  recurrence4QuotientConstant_coeff_306
  recurrence4QuotientConstant_coeff_307
  recurrence4QuotientConstant_coeff_308

attribute [local simp]
  recurrence4QuotientConstant_coeff_309
  recurrence4QuotientConstant_coeff_310
  recurrence4QuotientConstant_coeff_311
  recurrence4QuotientConstant_coeff_312
  recurrence4QuotientConstant_coeff_313
  recurrence4QuotientConstant_coeff_314
  recurrence4QuotientConstant_coeff_315
  recurrence4QuotientConstant_coeff_316
  recurrence4QuotientConstant_coeff_317
  recurrence4QuotientConstant_coeff_318
  recurrence4QuotientConstant_coeff_319
  recurrence4QuotientConstant_coeff_320
  recurrence4QuotientConstant_coeff_321
  recurrence4QuotientConstant_coeff_322
  recurrence4QuotientConstant_coeff_323
  recurrence4QuotientConstant_coeff_324
  recurrence4QuotientConstant_coeff_325
  recurrence4QuotientConstant_coeff_326
  recurrence4QuotientConstant_coeff_327
  recurrence4QuotientConstant_coeff_328
  recurrence4QuotientConstant_coeff_329
  recurrence4QuotientConstant_coeff_330
  recurrence4QuotientConstant_coeff_331
  recurrence4QuotientConstant_coeff_332
  recurrence4QuotientConstant_coeff_333
  recurrence4QuotientConstant_coeff_334
  recurrence4QuotientConstant_coeff_335
  recurrence4QuotientConstant_coeff_336
  recurrence4QuotientConstant_coeff_337
  recurrence4QuotientConstant_coeff_338
  recurrence4QuotientConstant_coeff_339
  recurrence4QuotientConstant_coeff_340
  recurrence4QuotientConstant_coeff_341
  recurrence4QuotientConstant_coeff_342
  recurrence4QuotientConstant_coeff_343
  recurrence4QuotientConstant_coeff_344
  recurrence4QuotientConstant_coeff_345
  recurrence4QuotientConstant_coeff_346

private theorem recurrence4Scalar0Main_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (277 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (277 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_277 :
    recurrence4Scalar0Main.coeff 277 =
      (((((8655522599276278811347099468 * 10 ^ 70 +
        2913207067861278755179597904544965464004293085243636699102570102068711) * 10 ^ 70 +
        5602574059751752891893752766861982167702151913928571757110130648202263) * 10 ^ 70 +
        0812698427356845297675428121015230037483473462594796930749279132136154) * 10 ^ 70 +
        0519018474275804959369083367368956292289510935639016949496076065613546) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (277 - x)) = _
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
    rw [show 117 = 16 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (278 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (278 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_278 :
    recurrence4Scalar0Main.coeff 278 =
      -(((((6726450539442572675168856616 * 10 ^ 70 +
        6390570004122698985489034692517444272869391892814348136966505537455111) * 10 ^ 70 +
        3357675924793995782970977535153260526689100957105590087070275897004290) * 10 ^ 70 +
        5899415290830839887202383018737654254969878927927892858865914020977462) * 10 ^ 70 +
        9006269851784420325202854419277603698283572588811457342138188132495236) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (278 - x)) = _
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
    rw [show 118 = 16 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (279 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (279 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_279 :
    recurrence4Scalar0Main.coeff 279 =
      (((((5146801278999889073525065706 * 10 ^ 70 +
        3963735351092309981868567781302544402194495198879583445769858728115438) * 10 ^ 70 +
        2628796245379337897044067224770430067269014731486214282990351391319485) * 10 ^ 70 +
        9807613512585873341558955320048767491997464622998486673842117597844052) * 10 ^ 70 +
        1449091825260576679821968981297379815399390528670970366762341352706141) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (279 - x)) = _
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
    rw [show 119 = 16 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (280 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (280 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_280 :
    recurrence4Scalar0Main.coeff 280 =
      -(((((3876836598710549174057804028 * 10 ^ 70 +
        9254629390845967883315951780158380004442803399822639399943347684267313) * 10 ^ 70 +
        0422514187975915803590715203496278633251984158140859350441295894713958) * 10 ^ 70 +
        5438036578139453827569767246659381664367774477444099146850521438585435) * 10 ^ 70 +
        7932541883291134605563012837010267949823195165000488064387152594153663) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (280 - x)) = _
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
    rw [show 120 = 16 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (281 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (281 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_281 :
    recurrence4Scalar0Main.coeff 281 =
      (((((2874206544155961510353377899 * 10 ^ 70 +
        1799452705938121664481531890805631885030553088598055207328756407384551) * 10 ^ 70 +
        7969870045097726219542998690373233029389971625234238084731338701362248) * 10 ^ 70 +
        6921814692259676248935422040476236488163085156914485394498305571651718) * 10 ^ 70 +
        6194763681483630239526293036895193923146817693430287121398329243710185) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (281 - x)) = _
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
    rw [show 121 = 16 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (282 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (282 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_282 :
    recurrence4Scalar0Main.coeff 282 =
      -(((((2096762053773696155389359383 * 10 ^ 70 +
        8391103793091113336376877869668435078195025296812347136521000012350349) * 10 ^ 70 +
        5508744697924963996155233313654625496602735010548583611721118590111845) * 10 ^ 70 +
        4583593459486256785875524012659263511610760742819449607140172098683596) * 10 ^ 70 +
        3063416430547851222705763783216129412621773545146013575228584332536629) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (282 - x)) = _
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
    rw [show 122 = 16 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (283 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (283 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_283 :
    recurrence4Scalar0Main.coeff 283 =
      (((((1504650104590878789724967685 * 10 ^ 70 +
        7045104536741854874181499339114016446594519477150376041504814116635072) * 10 ^ 70 +
        1511152345444120599191242471154249983017659582090963404032582936322650) * 10 ^ 70 +
        0150326896547556602942332500055395447424715337166187448051491381065270) * 10 ^ 70 +
        6971583569405619494905308869059693596313027482906116694129443255568384) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (283 - x)) = _
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
    rw [show 123 = 16 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (284 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (284 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_284 :
    recurrence4Scalar0Main.coeff 284 =
      -(((((1061719594019440059198693394 * 10 ^ 70 +
        0519915661416499997737980190456661810274879046403845838854121423440594) * 10 ^ 70 +
        2798191967495216924152691666990462565417133409272192972405208528681174) * 10 ^ 70 +
        1326465730265928723490834777968833068077428170265682137050467338293122) * 10 ^ 70 +
        3222567474545642630774886360966682394557417367981891192320579296969682) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (284 - x)) = _
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
    rw [show 124 = 16 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (285 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (285 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_285 :
    recurrence4Scalar0Main.coeff 285 =
      (((((736317258640736722900251606 * 10 ^ 70 +
        6443870656171904617872070343983595125269582070593004755321792306012397) * 10 ^ 70 +
        3521238941437568370366866742235842873984373294042279058950538653932414) * 10 ^ 70 +
        9096637310170396455263349807850212701555556086746486658048049944707724) * 10 ^ 70 +
        5532940979492172361023783176608681747523748980479707498707702495011708) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (285 - x)) = _
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
    rw [show 125 = 16 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (286 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (286 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_286 :
    recurrence4Scalar0Main.coeff 286 =
      -(((((501582996776778380256790365 * 10 ^ 70 +
        4171235169898424519082021944724027607622860933209403045217066567616742) * 10 ^ 70 +
        6888959616421399726522883051590934378460785036458179073351016554817081) * 10 ^ 70 +
        8247458930941472880440095532236506016955953766237611172390698433270137) * 10 ^ 70 +
        3320216095330464454513004444770404414682559479802446484736486500093573) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (286 - x)) = _
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
    rw [show 126 = 16 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (287 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (287 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_287 :
    recurrence4Scalar0Main.coeff 287 =
      (((((335365453425583745405195669 * 10 ^ 70 +
        8508869155648173779284755605027454085232940003821989013953401987885047) * 10 ^ 70 +
        2598010234786125771478506481928951451637913662923915705176960937274332) * 10 ^ 70 +
        6943752629918090485570562689737867883525321537208151521335588512975045) * 10 ^ 70 +
        8986728610197290711762538691421567111113833002495862197515224352958335) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (287 - x)) = _
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
    rw [show 127 = 16 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (288 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (288 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_288 :
    recurrence4Scalar0Main.coeff 288 =
      -(((((219875576404014074449752398 * 10 ^ 70 +
        2413694079903071565567497799719406708707139606390429521320318030354736) * 10 ^ 70 +
        5785427673668289521607287971220714112275401406663943359725111227201578) * 10 ^ 70 +
        4746516648944926641931695793729903434174212932620261541381026087774238) * 10 ^ 70 +
        3872922695284264738756882769728672683595328693736621757077165131341516) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (288 - x)) = _
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
    rw [show 128 = 16 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (289 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (289 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_289 :
    recurrence4Scalar0Main.coeff 289 =
      (((((141182578131743387170350811 * 10 ^ 70 +
        9067608853033578907325572969758421197467921698777468341437500465195589) * 10 ^ 70 +
        2587571006530455755523790594682827546645423770333738773385088178683094) * 10 ^ 70 +
        3136185989981359439738970363490446037501260593571866883502040494563158) * 10 ^ 70 +
        2578429750170974921693103804125673721574683106568439423893218277332087) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (289 - x)) = _
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
    rw [show 129 = 16 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (290 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (290 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_290 :
    recurrence4Scalar0Main.coeff 290 =
      -(((((88637707745398620426939694 * 10 ^ 70 +
        9128254414236669636268767565447302149613849201951323630743962601938453) * 10 ^ 70 +
        5934479035682336736778642719828502571795302577692991483936279837897170) * 10 ^ 70 +
        1575910605535568498180457757791710470144942144612933398733418524206267) * 10 ^ 70 +
        7440648767424870423816232830427050138713850562663136325793550240104249) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (290 - x)) = _
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
    rw [show 130 = 16 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (291 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (291 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_291 :
    recurrence4Scalar0Main.coeff 291 =
      (((((54290174121050280163231046 * 10 ^ 70 +
        1009428123793588581528496851775544339797265201315635610492629525067238) * 10 ^ 70 +
        5683164505730155113016883984633404857076443041571273624987450865864228) * 10 ^ 70 +
        1389313407968988228086126352568603483254470745429217383352579436744942) * 10 ^ 70 +
        0451171179929950011254878817608295089759896535864663787486632938742033) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (291 - x)) = _
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
    rw [show 131 = 16 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (292 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (292 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_292 :
    recurrence4Scalar0Main.coeff 292 =
      -(((((32339269403049455661343512 * 10 ^ 70 +
        4124603392083756037059142439217025459816135038089705259609188834075520) * 10 ^ 70 +
        8190743105488696784651157248645447893352220655993481037389507868856199) * 10 ^ 70 +
        7452983353741510383535631033673295892737066700886541611326945707374261) * 10 ^ 70 +
        8412583726439799025217072659586591838129559983405052578598768206869931) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (292 - x)) = _
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
    rw [show 132 = 16 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (293 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (293 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_293 :
    recurrence4Scalar0Main.coeff 293 =
      (((((18649056686018448219407524 * 10 ^ 70 +
        7688166561354914613873338970164675851316744732175252118177244722255290) * 10 ^ 70 +
        5726503899445126238687290222280370885394609574039298871025611451338849) * 10 ^ 70 +
        5079907940538043982957711231492895571724317551188961701513937672792682) * 10 ^ 70 +
        6141923449763086905613550954692287048879462865647928732604532888043824) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (293 - x)) = _
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
    rw [show 133 = 16 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (294 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (294 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_294 :
    recurrence4Scalar0Main.coeff 294 =
      -(((((10337847867889493192741562 * 10 ^ 70 +
        9017498763270694786552268308071185501203291098527521474359248892110110) * 10 ^ 70 +
        6562138142016785730774962786780387023614884818200460390126487026865804) * 10 ^ 70 +
        0006799660940286527888740513135490853164424653976628579775991140796881) * 10 ^ 70 +
        0817325551164038862906719820286053298812596019127517388474366442744708) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (294 - x)) = _
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
    rw [show 134 = 16 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (295 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (295 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_295 :
    recurrence4Scalar0Main.coeff 295 =
      (((((5444339480736519766292045 * 10 ^ 70 +
        8214425552470402143232809617746040250437242789432537525851143642519138) * 10 ^ 70 +
        4652592440156695067158109133672398065088275211087164299237938714239208) * 10 ^ 70 +
        6618439587640432267633912026623439436063004497049828777286601251617451) * 10 ^ 70 +
        5021380851234514505744138602785958736825129824765237081372863212217553) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (295 - x)) = _
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
    rw [show 135 = 16 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (296 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (296 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_296 :
    recurrence4Scalar0Main.coeff 296 =
      -(((((2665426137482510851070439 * 10 ^ 70 +
        0999129489468950598385938036840456254016351807424496007264777619369741) * 10 ^ 70 +
        8833917628790723689279391800452161686928975827193773558990739708526135) * 10 ^ 70 +
        4867185055813279884554261585786514712623395751508059900493059121368788) * 10 ^ 70 +
        7294402469649570337387121734265926021100520560424954478874237722746573) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (296 - x)) = _
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
    rw [show 136 = 16 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (297 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (297 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_297 :
    recurrence4Scalar0Main.coeff 297 =
      (((((1156808678714015901918155 * 10 ^ 70 +
        8321441097964550912032004754621326214536207416678212469049433759433674) * 10 ^ 70 +
        3925816782471204497436076770189096883113650484733500124878901921018066) * 10 ^ 70 +
        0408477882951153806710551401622544934270329228338525297369321704946525) * 10 ^ 70 +
        8562219383075788782247585659343575699568666377917266833676661701024492) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (297 - x)) = _
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
    rw [show 137 = 16 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (298 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (298 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_298 :
    recurrence4Scalar0Main.coeff 298 =
      -(((((385870136888829256453883 * 10 ^ 70 +
        2530322057859327020592791476378358332514692927512834309342652879909575) * 10 ^ 70 +
        2189198467794042020305958985378786499769590924113220533541024718819901) * 10 ^ 70 +
        4440824727881281986560433350490042111769970374179895964353562798783738) * 10 ^ 70 +
        2754241827001469470443727194667795910132026614583677922292330754397218) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (298 - x)) = _
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
    rw [show 138 = 16 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (299 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (299 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_299 :
    recurrence4Scalar0Main.coeff 299 =
      (((((26224574678300755842770 * 10 ^ 70 +
        0981873338280275903203314404607423841422522345349536034112050156362026) * 10 ^ 70 +
        3489299922014694472032484956988648074368254569809323981468041918734130) * 10 ^ 70 +
        0999227764533052597249313441430883687066927582647705643445948270866508) * 10 ^ 70 +
        0877940016749313857830309900359735874948976224022669686699954920565163) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (299 - x)) = _
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
    rw [show 139 = 16 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (300 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (300 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_300 :
    recurrence4Scalar0Main.coeff 300 =
      (((((115746533961228421590195 * 10 ^ 70 +
        4659280008832592386333685306156690435217034509375315874085197379161103) * 10 ^ 70 +
        2713263164125181479455118589419173869580219515424986572444291014912766) * 10 ^ 70 +
        0361100568642337441372182243113666226936083461896403084376184026241469) * 10 ^ 70 +
        4374046530118734716055984807036558762762153404494092939440014384344156) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (300 - x)) = _
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
    rw [show 140 = 16 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (301 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (301 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_301 :
    recurrence4Scalar0Main.coeff 301 =
      -(((((150642881576481194457169 * 10 ^ 70 +
        7720922895768723182624116703729342794099782521163445033165952217738752) * 10 ^ 70 +
        4188457555904616744276020904686327054079341945405918712592402787498284) * 10 ^ 70 +
        5000043621341928248838601172982598698757304104189971814612733254862352) * 10 ^ 70 +
        3623367868420069460949002491293524764878635104545280089213567970087652) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (301 - x)) = _
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
    rw [show 141 = 16 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (302 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (302 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_302 :
    recurrence4Scalar0Main.coeff 302 =
      (((((138777569889727507263015 * 10 ^ 70 +
        9382832075217484561866645223026991424241953782402738357837364325378094) * 10 ^ 70 +
        0333178562143113176866725471995690863936157764843339572298681712848763) * 10 ^ 70 +
        4773269613329033441867592866602970247997716495122372021736404980984947) * 10 ^ 70 +
        2728888266211371207210367686343456904887909144511718583395390635801200) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (302 - x)) = _
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
    rw [show 142 = 16 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (303 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (303 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_303 :
    recurrence4Scalar0Main.coeff 303 =
      -(((((111078813538045498134178 * 10 ^ 70 +
        8677765512531565530009819875068159235015676544681763256089196775289662) * 10 ^ 70 +
        4338921666306508713595575378658249075855633616416291598591654011188156) * 10 ^ 70 +
        2580251251442499763965988932996260560356733674127062536776941722816128) * 10 ^ 70 +
        6757800609184230672693926789063354156330831887373030581485962032859178) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (303 - x)) = _
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
    rw [show 143 = 16 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (304 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (304 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_304 :
    recurrence4Scalar0Main.coeff 304 =
      (((((82018817251037684336264 * 10 ^ 70 +
        5929091192724838808011714161762788192866569453411299340274555895443272) * 10 ^ 70 +
        3309615799768768656034304272154709667620269356631919277242500634638624) * 10 ^ 70 +
        2429594745916105107666340999583965905365782354652531965889927987348999) * 10 ^ 70 +
        0357892822321212983839100652326147217057346563936091972707579202039159) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (304 - x)) = _
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
    rw [show 144 = 16 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (305 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (305 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_305 :
    recurrence4Scalar0Main.coeff 305 =
      -(((((57336139153211440772763 * 10 ^ 70 +
        8435718425024741634750523530074414251071523455472226658994644715489018) * 10 ^ 70 +
        3613644646428161043906987354150260769563891175469887472858431393492984) * 10 ^ 70 +
        8720455505549727581520761422712992918785220494465710518372245243730118) * 10 ^ 70 +
        3335849961275475333182068235474871196769307078972173940401685889665953) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (305 - x)) = _
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
    rw [show 145 = 16 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (306 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (306 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_306 :
    recurrence4Scalar0Main.coeff 306 =
      (((((38467194888837402115653 * 10 ^ 70 +
        1854805801827636201792026526061501275830835156734253307077471140426651) * 10 ^ 70 +
        5707549215714273035509327354962942947539236485131543245252027299078125) * 10 ^ 70 +
        8735376399001398285826767223986794250913395696671368095885713409611034) * 10 ^ 70 +
        4396690583766461512047141150133638531937128491602989242205377085377693) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (306 - x)) = _
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
    rw [show 146 = 16 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (307 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (307 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_307 :
    recurrence4Scalar0Main.coeff 307 =
      -(((((24968971241726878932254 * 10 ^ 70 +
        8595221368633817671159249370242272714128219515904210251456802135471848) * 10 ^ 70 +
        1402021513432849688307191405211543468747366807248555798062227462982542) * 10 ^ 70 +
        0204321585486326368182076809489007228388693269689166746588249601989542) * 10 ^ 70 +
        5495179091972492202962485641513732896511797803608747865210369370024299) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (307 - x)) = _
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
    rw [show 147 = 16 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (308 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (308 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_308 :
    recurrence4Scalar0Main.coeff 308 =
      (((((15762031548795338676648 * 10 ^ 70 +
        2114011299105661986665477212616353737706438651638620241351111930119433) * 10 ^ 70 +
        5606947575568265548366578948720567996684818819980315713748818975734608) * 10 ^ 70 +
        6782787819131230729945758845406352658589219905785944523779636029354804) * 10 ^ 70 +
        1656961124785966103717087254677926294410994628794202761801202905552911) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (308 - x)) = _
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
    rw [show 148 = 16 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (309 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (309 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_309 :
    recurrence4Scalar0Main.coeff 309 =
      -(((((9711214639921587205327 * 10 ^ 70 +
        5335541961331792641181739702137288926998840593604500245445654531411461) * 10 ^ 70 +
        5638494228674869800132972888120202002926817579424655842353969079596390) * 10 ^ 70 +
        0982638799817992828301287765404831547020655318658638974601790559101881) * 10 ^ 70 +
        3337557894303768122367247228420258980319994191388377379729053438919203) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (309 - x)) = _
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
    rw [show 149 = 16 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (310 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (310 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_310 :
    recurrence4Scalar0Main.coeff 310 =
      (((((5854805746344612140409 * 10 ^ 70 +
        5774093296924176695971097831182964817486758014253478770911533802486393) * 10 ^ 70 +
        7620763579773698954343955956246711971967969038311218607408113651265433) * 10 ^ 70 +
        4559575475455285635559739566773638298252201894536421238994942943520806) * 10 ^ 70 +
        6672770683069232382494218751963998060217053033372138107514802525494625) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (310 - x)) = _
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
    rw [show 150 = 16 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (311 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (311 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_311 :
    recurrence4Scalar0Main.coeff 311 =
      -(((((3460996738315403120738 * 10 ^ 70 +
        4693103761886092323211124011925588516547898820336706140152679868108193) * 10 ^ 70 +
        3006775074882126653300974093358192701738410284788985102888684926052163) * 10 ^ 70 +
        9575364148765267584828598120967447592034756487093195706755220936260284) * 10 ^ 70 +
        6022059200360008514865278197975840373187541492848590667520210462186747) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (311 - x)) = _
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
    rw [show 151 = 16 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (312 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (312 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_312 :
    recurrence4Scalar0Main.coeff 312 =
      (((((2009382175563633478846 * 10 ^ 70 +
        3709280676339966354660265564251865785106012327710971813082092428730364) * 10 ^ 70 +
        4940288973215779002167336917525042399320957851946990947224149059041552) * 10 ^ 70 +
        1906565637923740092151480020954008540653874338235424704094233071754050) * 10 ^ 70 +
        9889413933363900205076843705410344524996530624353861504670427140031677) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (312 - x)) = _
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
    rw [show 152 = 16 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (313 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (313 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_313 :
    recurrence4Scalar0Main.coeff 313 =
      -(((((1147484285448696535356 * 10 ^ 70 +
        3043754522491883125352363677498880380537549386197247888958901910079477) * 10 ^ 70 +
        1302406245872566289296720734583965703507691882086149318641436262695635) * 10 ^ 70 +
        8820770552590450389763425803912340657453061926784107227293367364674611) * 10 ^ 70 +
        1138507653209809828665142807370742991102165105378120916807612708866953) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (313 - x)) = _
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
    rw [show 153 = 16 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (314 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (314 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_314 :
    recurrence4Scalar0Main.coeff 314 =
      (((((645495581404073329867 * 10 ^ 70 +
        2772785141712157800532335205563299066140293060877188191266651641944273) * 10 ^ 70 +
        7727798812528648859756912489014858801142995195056328829667825752102128) * 10 ^ 70 +
        1912403407579162567480485139731591969487467516170064380571792560602551) * 10 ^ 70 +
        4654548332927390816359060304265558157413375726583233001855372648914908) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (314 - x)) = _
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
    rw [show 154 = 16 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (315 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (315 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_315 :
    recurrence4Scalar0Main.coeff 315 =
      -(((((358249997323423513020 * 10 ^ 70 +
        7249459168469871739274956276169164128714648593402196143427506538640457) * 10 ^ 70 +
        0993431456370274135551381965383142531598416055694015067790546905144320) * 10 ^ 70 +
        8796637113475539716624423452282885240971707500107512152570991934263619) * 10 ^ 70 +
        7629731612280373664863733451532975861748467344562648513604947753472166) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (315 - x)) = _
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
    rw [show 155 = 16 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (316 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (316 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_316 :
    recurrence4Scalar0Main.coeff 316 =
      (((((196519634645896512827 * 10 ^ 70 +
        8205298588034154363846956514542302824189985348080868535122568168746031) * 10 ^ 70 +
        4066025465607033313425748945440225377237953794957067437785386926482707) * 10 ^ 70 +
        3769149241926929743092324543470182466638863387704298533687144407510006) * 10 ^ 70 +
        5091040101453408860047663429950781565431075428141855599775352937172231) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (316 - x)) = _
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
    rw [show 156 = 16 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (317 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (317 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_317 :
    recurrence4Scalar0Main.coeff 317 =
      -(((((106776673191604576864 * 10 ^ 70 +
        1380753688051804974647516859096209770837954783179446970485880511952300) * 10 ^ 70 +
        9348151771218028194183848888353306723953761063577510141745713751625492) * 10 ^ 70 +
        4187970073737748772581733871274529534564716517550727680661685320958447) * 10 ^ 70 +
        4317874816066275774896164620590571119399411566252638608638669652001284) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (317 - x)) = _
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
    rw [show 157 = 16 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (318 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (318 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_318 :
    recurrence4Scalar0Main.coeff 318 =
      (((((57610383413981833400 * 10 ^ 70 +
        7933327879043746425288298756359608284095485478980337326116642852718732) * 10 ^ 70 +
        2255501889850190922919218139445031773595093335468173691423028684432144) * 10 ^ 70 +
        0220753362843478640931513173140514474636036917857139908467469209334850) * 10 ^ 70 +
        5651980621701468176463800058503131644539810114795787779262584347163882) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (318 - x)) = _
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
    rw [show 158 = 16 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (319 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (319 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_319 :
    recurrence4Scalar0Main.coeff 319 =
      -(((((30958097155528230078 * 10 ^ 70 +
        7858375345093829489310279095691871928644198548898365844469607973209105) * 10 ^ 70 +
        6914208780869479156201800759889666853667484634809671624620645165604166) * 10 ^ 70 +
        5948344713607108179145944576161622187918612707105818356612959420190239) * 10 ^ 70 +
        3650586289201891391620885606626650287229868820997750958992212581619314) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (319 - x)) = _
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
    rw [show 159 = 16 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (320 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (320 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_320 :
    recurrence4Scalar0Main.coeff 320 =
      (((((16624753873284471845 * 10 ^ 70 +
        4329029895554772450783938411259680846237828172101341223185651270919539) * 10 ^ 70 +
        8641586970130280991177223289098876822278446096522686507250114758904273) * 10 ^ 70 +
        0743545332888018190669429286344392492131493294039482569998545793156133) * 10 ^ 70 +
        5821926979027039615824782088115356964694437677746687171778052734300963) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (320 - x)) = _
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
    rw [show 160 = 16 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (321 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (321 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_321 :
    recurrence4Scalar0Main.coeff 321 =
      -(((((8953172881090783493 * 10 ^ 70 +
        4009486032316554850560417882071775192299752508289244141208348064938647) * 10 ^ 70 +
        8807306600769249106976843702309529961489557918062268416789779761272416) * 10 ^ 70 +
        1895925108679886962916234832167012728820072951404322423353138098312249) * 10 ^ 70 +
        9712956281715955697908296047594671985157877040940530559483501220176941) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (321 - x)) = _
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
    rw [show 161 = 16 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (322 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (322 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_322 :
    recurrence4Scalar0Main.coeff 322 =
      (((((4851680400047337302 * 10 ^ 70 +
        6236101608266855298702604040894710107966339737507887470417043505318495) * 10 ^ 70 +
        1786761385267240171155401928401928826750658539003209815914082072089175) * 10 ^ 70 +
        5489420439055363395236079381390288459246503074805610506154088698198136) * 10 ^ 70 +
        2547007914778883104656668914581131928792700258679154268181258543796495) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (322 - x)) = _
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
    rw [show 162 = 16 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (323 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (323 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_323 :
    recurrence4Scalar0Main.coeff 323 =
      -(((((2652572313993869432 * 10 ^ 70 +
        3876807110247685232639841174988882158099150320374095877065488958319502) * 10 ^ 70 +
        4669424573320442749976488658550255195132851834697593235674638237874751) * 10 ^ 70 +
        6938578877910529370654940660074409399899772603738771912828278648218436) * 10 ^ 70 +
        2053744777083973454133550122453995350075559002492489174303064652343841) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (323 - x)) = _
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
    rw [show 163 = 16 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (324 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (324 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_324 :
    recurrence4Scalar0Main.coeff 324 =
      (((((1465467680961098030 * 10 ^ 70 +
        6771369106946290862594632688514884980056229420321250938691755815631840) * 10 ^ 70 +
        0889380237756859918232649660361858311185038202076947046637862420857601) * 10 ^ 70 +
        4644046644102379606177953907948771066902825110277470334429103783812923) * 10 ^ 70 +
        9929650028627591943773013710176617127448741184127940362742388476353423) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (324 - x)) = _
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
    rw [show 164 = 16 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (325 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (325 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_325 :
    recurrence4Scalar0Main.coeff 325 =
      -(((((818209732884394916 * 10 ^ 70 +
        0741800085181816027836436233597902010983878775475021692614382805486392) * 10 ^ 70 +
        7179938124958185308984864581737681098645306895668596327953756802650177) * 10 ^ 70 +
        1530086053821339909228216229459394315574378524518815884799008858151335) * 10 ^ 70 +
        5131768846998606225644849653299273819270453139618481291315353347678003) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (325 - x)) = _
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
    rw [show 165 = 16 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (326 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (326 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_326 :
    recurrence4Scalar0Main.coeff 326 =
      (((((461038087234618026 * 10 ^ 70 +
        1313090122305773921245031369669702359385800393985156058661254930080440) * 10 ^ 70 +
        7850032133566574182477009770656860937463833710544932664480121925141450) * 10 ^ 70 +
        3049988834349893805576425715459608449831404747776410055172424004756747) * 10 ^ 70 +
        5942492655436142981969483393456857624561320247580108168609899977000367) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (326 - x)) = _
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
    rw [show 166 = 16 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (327 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (327 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_327 :
    recurrence4Scalar0Main.coeff 327 =
      -(((((261501275415638026 * 10 ^ 70 +
        1019717520759204154250282847704894409204028547018500923133627280577412) * 10 ^ 70 +
        6932312302215502516979111200555828814515256874435909781053620107683913) * 10 ^ 70 +
        9200486080933578579456093780606601904196194235418435246821005026722690) * 10 ^ 70 +
        8872339696920370650890558446997462708276591996180746801144360245201747) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (327 - x)) = _
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
    rw [show 167 = 16 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (328 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (328 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_328 :
    recurrence4Scalar0Main.coeff 328 =
      (((((148810791872770289 * 10 ^ 70 +
        8932516608052616981045198457249838548669877432377242103765220336760227) * 10 ^ 70 +
        1947682671908948016001774947947611408719301309359884328714583081490125) * 10 ^ 70 +
        5512337935894245183478966821341790878942415597122948285965851518897909) * 10 ^ 70 +
        7550599524028479612033841940348523836398075968236620195333415370190637) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (328 - x)) = _
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
    rw [show 168 = 16 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (329 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (329 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_329 :
    recurrence4Scalar0Main.coeff 329 =
      -(((((84658320589887583 * 10 ^ 70 +
        4088416817424897263689281238781894809754419193046844164070311364196481) * 10 ^ 70 +
        2681541387013921862707714068336364235660785058561018921341747241624632) * 10 ^ 70 +
        3600936993269608758030784622380404955172965000764091741213704733941589) * 10 ^ 70 +
        8844755505421373616561427513630260122516425721873876663312071913429513) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (329 - x)) = _
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
    rw [show 169 = 16 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (330 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (330 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_330 :
    recurrence4Scalar0Main.coeff 330 =
      (((((47983854090135507 * 10 ^ 70 +
        3665305210652681248921987087994426918778164470487092676435102273969444) * 10 ^ 70 +
        1136943165691628434857742467948137053976897473151863156938949486829588) * 10 ^ 70 +
        3374901995992484648379779571492532046069471234696479156355256218453227) * 10 ^ 70 +
        3383596131237052988098444362745866904557424495066458746812875036474004) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (330 - x)) = _
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
    rw [show 170 = 16 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (331 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (331 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_331 :
    recurrence4Scalar0Main.coeff 331 =
      -(((((27014565131625658 * 10 ^ 70 +
        6973138997300841562396366295337530180143768878461896608904336772408687) * 10 ^ 70 +
        7623569520093175392815558977210510875603824604558477199845982521930356) * 10 ^ 70 +
        8633296369269778755126535207904914063383149207109447015424472368675258) * 10 ^ 70 +
        3988226608768284703297907857179572957100681027330969961814237280273514) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (331 - x)) = _
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
    rw [show 171 = 16 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (332 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (332 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_332 :
    recurrence4Scalar0Main.coeff 332 =
      (((((15068920576032673 * 10 ^ 70 +
        2830323721946742171451086441209980960448595887487161663311877724545097) * 10 ^ 70 +
        2397915478287676101261359397216765394476087647885942048103791099581942) * 10 ^ 70 +
        1604189636592723457836956016462136722816358833046814541777655821365761) * 10 ^ 70 +
        2376090586430467909186383802233021719291239096883807737943207071063360) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (332 - x)) = _
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
    rw [show 172 = 16 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (333 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (333 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_333 :
    recurrence4Scalar0Main.coeff 333 =
      -(((((8311318352549153 * 10 ^ 70 +
        7863728257942956266561502197856095758587350685432070120781268230666118) * 10 ^ 70 +
        1228588992654369652774656103303852644702862875204152478220799085965201) * 10 ^ 70 +
        6381900142471107519630396532414151948186547268840876686777677494556549) * 10 ^ 70 +
        8723435588662153689549817065995273398997402077979769998893078140762038) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (333 - x)) = _
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
    rw [show 173 = 16 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (334 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (334 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_334 :
    recurrence4Scalar0Main.coeff 334 =
      (((((4525626902120899 * 10 ^ 70 +
        3230738860795925036243668720915590994206323022393151707184259644218453) * 10 ^ 70 +
        2671945368543225941921713891123373772570072967892282225137290545233615) * 10 ^ 70 +
        1488569063351393699287907141638403002542523963182007755209186295093274) * 10 ^ 70 +
        2289725216415865031099005205685159502104519568879393537033861823521715) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (334 - x)) = _
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
    rw [show 174 = 16 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (335 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (335 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_335 :
    recurrence4Scalar0Main.coeff 335 =
      -(((((2429896605482107 * 10 ^ 70 +
        8305403052866005465263072993362183294775885368586101235255728553691860) * 10 ^ 70 +
        8748602012330098164426658691836746335924904961930395664767496501795839) * 10 ^ 70 +
        2955237043688575425020067385134176380184179330247694850945962290708597) * 10 ^ 70 +
        8990819963050133336448409726568244973016358774933487949354252965582363) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (335 - x)) = _
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
    rw [show 175 = 16 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (336 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (336 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_336 :
    recurrence4Scalar0Main.coeff 336 =
      (((((1285296373263172 * 10 ^ 70 +
        7232608922704346675049612231208392498778964738501171631882012653450598) * 10 ^ 70 +
        0046565044083288909723436391280841729197168306292447354001596845971289) * 10 ^ 70 +
        6907735324040254373568567223319429519839303942644514529321305702392564) * 10 ^ 70 +
        1846491357165540322839461626203903675564512760579461812865468870992164) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (336 - x)) = _
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
    rw [show 176 = 16 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (337 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (337 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_337 :
    recurrence4Scalar0Main.coeff 337 =
      -(((((669309750864956 * 10 ^ 70 +
        1655137897445877063161503048149018996347674212099551310523770705497381) * 10 ^ 70 +
        2547611060547754960047656825746982178638883789190494717890432492733674) * 10 ^ 70 +
        3940401118266215736756562036368371719514387433692424562220267687627816) * 10 ^ 70 +
        2703841172468696233978507750883120028641945908231171401171344557432803) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (337 - x)) = _
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
    rw [show 177 = 16 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (338 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (338 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_338 :
    recurrence4Scalar0Main.coeff 338 =
      (((((342949922362243 * 10 ^ 70 +
        0443945828185621899282430987038620269071581597928063555595352330691152) * 10 ^ 70 +
        7799081703029850172738234935885294268244732114830053990365239950934219) * 10 ^ 70 +
        2444104707045848524077079444552073961596511054645032520793033190534465) * 10 ^ 70 +
        8997828040119081525917413310737427738536481025849571680220132779708743) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (338 - x)) = _
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
    rw [show 178 = 16 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (339 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (339 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_339 :
    recurrence4Scalar0Main.coeff 339 =
      -(((((172835669764725 * 10 ^ 70 +
        0389271136846012791182617400705475791008559399357074253230673977641009) * 10 ^ 70 +
        0166667787427866180380181224280838645343110221597470120670012680180902) * 10 ^ 70 +
        8620610783651635948346817457854474611674104205166259658464187906706384) * 10 ^ 70 +
        9809132913752413040619313463247927641940652412636273362901332346810794) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (339 - x)) = _
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
    rw [show 179 = 16 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (340 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (340 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_340 :
    recurrence4Scalar0Main.coeff 340 =
      (((((85641838320593 * 10 ^ 70 +
        1408015483942806124582007971261120368025812484461700282779756249842259) * 10 ^ 70 +
        2016279968781398093665968779469250182369170446525075157961125404243831) * 10 ^ 70 +
        6182483353100454036305653419892088236882219577538272810350521147914413) * 10 ^ 70 +
        1644387891798750698631861445475399027818990989619940652134719461410069) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (340 - x)) = _
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
    rw [show 180 = 16 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (341 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (341 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_341 :
    recurrence4Scalar0Main.coeff 341 =
      -(((((41711684834977 * 10 ^ 70 +
        1209822143783894211040878594224778655845928358147530236469794348185819) * 10 ^ 70 +
        5594935101527814375428030054740999409312149378395986909106043400798229) * 10 ^ 70 +
        5730873653142773734834398913037530579874354999094698938370370922122244) * 10 ^ 70 +
        0896546916609947486680018400307598818051949947873981841364980230966245) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (341 - x)) = _
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
    rw [show 181 = 16 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (342 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (342 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_342 :
    recurrence4Scalar0Main.coeff 342 =
      (((((19963014259772 * 10 ^ 70 +
        8057397470788796326113301909804104053308841315366464500300457138525515) * 10 ^ 70 +
        7040039677913672122877477618258616665590465712638196998056568328157875) * 10 ^ 70 +
        6026099335298582991160014584416898345393761560488917500750903339501669) * 10 ^ 70 +
        1455976589517647071793536242253266940616648389753450602655786408232448) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (342 - x)) = _
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
    rw [show 182 = 16 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (343 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (343 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_343 :
    recurrence4Scalar0Main.coeff 343 =
      -(((((9385750269045 * 10 ^ 70 +
        7294495796210869223840277450050001713051763351700444029738825202139850) * 10 ^ 70 +
        8510445388630084490470858271012337394522734772555853835933563650949377) * 10 ^ 70 +
        7229169301854606720644620065206284531294744912961111062096751476408829) * 10 ^ 70 +
        2478841271013367101422659941857162378136563456860278427222209181897343) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (343 - x)) = _
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
    rw [show 183 = 16 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (344 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (344 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_344 :
    recurrence4Scalar0Main.coeff 344 =
      (((((4333695355405 * 10 ^ 70 +
        3272250080994465663740852567189655521098084514636878393800671852147755) * 10 ^ 70 +
        9738943993615263421002701694804605133405725754096919670638718098029839) * 10 ^ 70 +
        6315897423015739738337416893549559734047061186507249589850527799571881) * 10 ^ 70 +
        1643600542032086297420514964249836259909661434130924794922733100637052) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (344 - x)) = _
  rw [show 345 = 1 +
    344 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 344 = 32 +
      312 by norm_num, Finset.sum_range_add]
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
    rw [show 184 = 16 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (345 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (345 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_345 :
    recurrence4Scalar0Main.coeff 345 =
      -(((((1964515830109 * 10 ^ 70 +
        5819361534418221693902090926543201513316912295294318800008871594148670) * 10 ^ 70 +
        1945624179898694065007239165069780447299627656260114112810107922546551) * 10 ^ 70 +
        0048608075174456848256452596281742963469093551379002766900141729090297) * 10 ^ 70 +
        0532136578798222131568215573993310074488783972698236702790303054202291) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (345 - x)) = _
  rw [show 346 = 1 +
    345 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 345 = 32 +
      313 by norm_num, Finset.sum_range_add]
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
    rw [show 185 = 16 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (346 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (346 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_346 :
    recurrence4Scalar0Main.coeff 346 =
      (((((873991501845 * 10 ^ 70 +
        6996920013163988726944570077233974971689070819949005041312677494787885) * 10 ^ 70 +
        7565337796994479807039179585921327759699482816578029471293438012148193) * 10 ^ 70 +
        6031060315034529906918215559027795937102226226877940046720577566561121) * 10 ^ 70 +
        7148987302450175144461385147078732297487120059407993287892619614994178) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (346 - x)) = _
  rw [show 347 = 1 +
    346 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 346 = 32 +
      314 by norm_num, Finset.sum_range_add]
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
    rw [show 186 = 16 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (347 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (347 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_347 :
    recurrence4Scalar0Main.coeff 347 =
      -(((((381454804180 * 10 ^ 70 +
        3067061455418643277437975176222641220104802356353217725361400319262272) * 10 ^ 70 +
        7313376295211919001112584940474401170972962350764433406300691152684123) * 10 ^ 70 +
        7723872403506792491300840179252796920711754766955009981157926972725603) * 10 ^ 70 +
        3074802203918713729048605223407809525666032276787033510752762103663828) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (347 - x)) = _
  rw [show 348 = 1 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 16 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (348 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (348 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_348 :
    recurrence4Scalar0Main.coeff 348 =
      (((((163258117992 * 10 ^ 70 +
        4736202974401253630431739384551979145814852568683182788757887149244412) * 10 ^ 70 +
        3861799732753990158544186020432471063480268762615593822912228449048393) * 10 ^ 70 +
        3699565408722498156732398632291811689543863586405283569341586191005158) * 10 ^ 70 +
        3481829241873012791010697042237974560875021617358152554457789176756992) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (348 - x)) = _
  rw [show 349 = 2 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 15 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (349 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (349 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_349 :
    recurrence4Scalar0Main.coeff 349 =
      -(((((68485291458 * 10 ^ 70 +
        6711643731726708776924429260177186967547573231184046595149394257438700) * 10 ^ 70 +
        4834766984934901249440221959047547788062148038803921436894701298011171) * 10 ^ 70 +
        5179308139048330489024846905907057187627550026267902510846281819623703) * 10 ^ 70 +
        0004937713057703260398356710988999600686884208141319759874174588183110) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (349 - x)) = _
  rw [show 350 = 3 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 14 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (350 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (350 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_350 :
    recurrence4Scalar0Main.coeff 350 =
      (((((28144571709 * 10 ^ 70 +
        0213497559858259760210065567468190939393636196092193779069637516037099) * 10 ^ 70 +
        2169188890235769541002340366780915141242634878758989378494800552301741) * 10 ^ 70 +
        6861539671787971854857210399176535454960275750161579762438679098088752) * 10 ^ 70 +
        4621206702195345932717688218224026138868782615781483178268988431643584) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (350 - x)) = _
  rw [show 351 = 4 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 13 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (351 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (351 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_351 :
    recurrence4Scalar0Main.coeff 351 =
      -(((((11325373892 * 10 ^ 70 +
        4330782262748878082295183204680029739542224146018410411840937052726799) * 10 ^ 70 +
        8569337265251710569818856236900189818094502209377413505364017733422720) * 10 ^ 70 +
        5922802671591648287132589106772930094417375891480449803596854385016829) * 10 ^ 70 +
        4394919080980915525724063055005097164643434456132770796123878793685555) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (351 - x)) = _
  rw [show 352 = 5 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 12 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (352 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (352 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_352 :
    recurrence4Scalar0Main.coeff 352 =
      (((((4460504472 * 10 ^ 70 +
        9622405940383050346920937490335101624588959464046559226728070203516877) * 10 ^ 70 +
        9069960536223493445175828635935224848005079967025457213792972993707378) * 10 ^ 70 +
        8365927164249954467447235405370843260244440567360244960174719137164892) * 10 ^ 70 +
        1433760780648682989046227155311450882750269334332330665805040565227161) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (352 - x)) = _
  rw [show 353 = 6 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 11 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (353 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (353 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_353 :
    recurrence4Scalar0Main.coeff 353 =
      -(((((1719003037 * 10 ^ 70 +
        9399211482844304035368770803500356551053106192006231471208842331407799) * 10 ^ 70 +
        7050331311938284887635553544894907633387039511375583944647014049957482) * 10 ^ 70 +
        7145144869791898447938135241309237447569594144012646330247226788288167) * 10 ^ 70 +
        9706616347108431876486910982585626028817483952602507488001652110872190) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (353 - x)) = _
  rw [show 354 = 7 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 10 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (354 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (354 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_354 :
    recurrence4Scalar0Main.coeff 354 =
      (((((648304059 * 10 ^ 70 +
        6896842405259993320674317731501197733347803408115321128209767399789029) * 10 ^ 70 +
        0043487853522241719283180348636009713262147489734809180021831922308835) * 10 ^ 70 +
        5000984152336906473719388417432340247019549818049221604607351913082703) * 10 ^ 70 +
        0622730898733675246318920958263765369779855366076383137303549477240392) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (354 - x)) = _
  rw [show 355 = 8 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 9 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (355 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (355 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_355 :
    recurrence4Scalar0Main.coeff 355 =
      -(((((239468796 * 10 ^ 70 +
        3017236773840912118150580298365267917917025839028503141037899609698987) * 10 ^ 70 +
        6580381095305175848180389686725544759691668688145169499144054775063582) * 10 ^ 70 +
        7369366567850793695069125211562870347466853831814546122756932089465566) * 10 ^ 70 +
        3292243712529387930692846338818693179144127186237285153201516221313618) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (355 - x)) = _
  rw [show 356 = 9 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 8 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (356 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (356 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_356 :
    recurrence4Scalar0Main.coeff 356 =
      (((((86817777 * 10 ^ 70 +
        8954950981549628137956439807066741889102750274680080519148387174815189) * 10 ^ 70 +
        9514734048394909954412287330491582967143838428015875724154764399964968) * 10 ^ 70 +
        2560396084874305998363983090417681580989943355761278885035556281938350) * 10 ^ 70 +
        6381856991115585933703222764348845172602076481129002706618942870179461) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (356 - x)) = _
  rw [show 357 = 10 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 7 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (357 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (357 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_357 :
    recurrence4Scalar0Main.coeff 357 =
      -(((((31026983 * 10 ^ 70 +
        4800364359871912782344399177865246359593062432037677804061020968624060) * 10 ^ 70 +
        0960637257279215216425186783290862135664576501032448322858915011219460) * 10 ^ 70 +
        2985757320888975099430641665295049952360511405419271359395034666465468) * 10 ^ 70 +
        7174343467056545794493366952473984231128803547024742684260503546142732) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (357 - x)) = _
  rw [show 358 = 11 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 6 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (358 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (358 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_358 :
    recurrence4Scalar0Main.coeff 358 =
      (((((11016203 * 10 ^ 70 +
        3988573795974548584156792270876105613110577578946033839597055467798937) * 10 ^ 70 +
        0767708382019161306225360560265620314352254748033018356072165645387193) * 10 ^ 70 +
        1812027294977065722568450561740280422006376903080705577401963404088348) * 10 ^ 70 +
        0610701464490053904882199018158923412488664465065920779248706393341470) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (358 - x)) = _
  rw [show 359 = 12 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 5 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (359 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (359 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_359 :
    recurrence4Scalar0Main.coeff 359 =
      -(((((3934907 * 10 ^ 70 +
        8149303587260610871543958977955093097933629599291402614833755533265509) * 10 ^ 70 +
        4397036240390748436279046004067378733532690119625014440847244562021819) * 10 ^ 70 +
        6006985120074058907708922965308583894002932144556129998969361892367061) * 10 ^ 70 +
        0128076775502678110620710704551554766711367262994462177020728815464415) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (359 - x)) = _
  rw [show 360 = 13 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 4 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (360 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (360 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_360 :
    recurrence4Scalar0Main.coeff 360 =
      (((((1438774 * 10 ^ 70 +
        9048902636336278682057297807610159268098102156713395240045741687468530) * 10 ^ 70 +
        0978620083032779338198297652609020805966066218845231101998312748521879) * 10 ^ 70 +
        3454228838314298677357293589823696671090800669626379676948850736377894) * 10 ^ 70 +
        9454557113911959096444842918359661164767677923151727566995373172802422) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (360 - x)) = _
  rw [show 361 = 14 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 3 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (361 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (361 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_361 :
    recurrence4Scalar0Main.coeff 361 =
      -(((((548895 * 10 ^ 70 +
        4886840600120930603072490222752051714313880442998589514864208017398671) * 10 ^ 70 +
        7953364855459157685814978315428705703431075601781628630039277167199207) * 10 ^ 70 +
        8001545116760313378379453613713947095261319894470672863151844077869176) * 10 ^ 70 +
        0850902783797091301564715723962521711620165979570996158643912725831192) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (361 - x)) = _
  rw [show 362 = 15 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 2 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (362 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (362 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_362 :
    recurrence4Scalar0Main.coeff 362 =
      (((((221477 * 10 ^ 70 +
        1608583835835543994874767835713894871336483324476142781097969970346719) * 10 ^ 70 +
        2524008350596761728068630145639654432799530498150981784305353604052905) * 10 ^ 70 +
        8857858388705235258489645962693060764590333532081130143210317439103345) * 10 ^ 70 +
        5157451304080360975632087686193347167042459965764858158036631685807696) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (362 - x)) = _
  rw [show 363 = 16 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 187 = 1 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (363 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (363 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_363 :
    recurrence4Scalar0Main.coeff 363 =
      -(((((94597 * 10 ^ 70 +
        5385548805230266163526879489323997917321038203256417685105743444746155) * 10 ^ 70 +
        0163237510881984212142676638730689407995679392910734156240961676003993) * 10 ^ 70 +
        0510630148828198494205705493714535581642181035542082397395523780621487) * 10 ^ 70 +
        2815924918433782522240126455229321591747667443587532737159550439924180) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (363 - x)) = _
  rw [show 364 = 17 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
  rw [recurrence4Scalar0Main_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (364 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (364 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_364 :
    recurrence4Scalar0Main.coeff 364 =
      (((((42237 * 10 ^ 70 +
        6813375783286628931446815012402746384410361918175762317076216616144747) * 10 ^ 70 +
        8549191800672455405192536906977504974725593559484973979618665366579383) * 10 ^ 70 +
        2786933633264184444091971270454378925464983725282029300380181173060173) * 10 ^ 70 +
        2277787735499585435982099880918735284534768465584469192909697083387365) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (364 - x)) = _
  rw [show 365 = 18 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 31 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (365 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (365 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_365 :
    recurrence4Scalar0Main.coeff 365 =
      -(((((19338 * 10 ^ 70 +
        6971930512623973843235404786719410393588506407832439926537815855052215) * 10 ^ 70 +
        4064543985223639750577769357889875465022142961257991042375373972989969) * 10 ^ 70 +
        2812816302462086576175281497439740440992450349039233092072165157822952) * 10 ^ 70 +
        1025222667636709538171888779578382630256330534497505323321035954100685) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (365 - x)) = _
  rw [show 366 = 19 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 30 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (366 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (366 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_366 :
    recurrence4Scalar0Main.coeff 366 =
      (((((8913 * 10 ^ 70 +
        7545662282974860960444894983572200675966565794269436441426704531516339) * 10 ^ 70 +
        0846295603295231712680562772098055027617702677162511966486111009449027) * 10 ^ 70 +
        5437419886628727821678389320988104317433398260040006061178768712456037) * 10 ^ 70 +
        9199769256002685092136276970128442549357476121953262468808718949543991) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (366 - x)) = _
  rw [show 367 = 20 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 29 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (367 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (367 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_367 :
    recurrence4Scalar0Main.coeff 367 =
      -(((((4079 * 10 ^ 70 +
        2752023758817631471124325993741224781313071319093214145610016557910239) * 10 ^ 70 +
        7275515123803274658448495167209073566444828782009495328843533257613880) * 10 ^ 70 +
        3941011145467333722716724813350494462733554568302542350080557108430505) * 10 ^ 70 +
        5036753566377025152374023522972452696276398081734617364358462386315886) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (367 - x)) = _
  rw [show 368 = 21 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 28 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (368 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (368 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_368 :
    recurrence4Scalar0Main.coeff 368 =
      (((((1836 * 10 ^ 70 +
        7898854074692374760499096834242856541270875795729345559648850661204739) * 10 ^ 70 +
        9595710068450322088999517306883911588174119136220509125449728592854935) * 10 ^ 70 +
        8887391378609599499020446074400738967352817236804688581531779177512877) * 10 ^ 70 +
        8946451144818961365756475687109499388418464135820732492151688733546795) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (368 - x)) = _
  rw [show 369 = 22 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 27 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (369 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (369 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_369 :
    recurrence4Scalar0Main.coeff 369 =
      -(((((809 * 10 ^ 70 +
        3036812085094288825408528538373952476749516880038679747546771631423438) * 10 ^ 70 +
        0815753809483302331999980476556129235373831938375667144419397690528059) * 10 ^ 70 +
        1569546556756747990712760367352563409888905241537249341565391624500272) * 10 ^ 70 +
        6145056349660602855041865787282531658351481747392080619166722528245867) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (369 - x)) = _
  rw [show 370 = 23 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 26 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (370 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (370 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_370 :
    recurrence4Scalar0Main.coeff 370 =
      (((((347 * 10 ^ 70 +
        8102790221713256907965793014286000885518425461071094268599638829383985) * 10 ^ 70 +
        3483469979390542990438489245479958905370199862511004698718517002458220) * 10 ^ 70 +
        1820137364411935735792900186960479955397732326303371148881640953900495) * 10 ^ 70 +
        4442008127607657952157007273027815680610653129492039505847266393326429) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (370 - x)) = _
  rw [show 371 = 24 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 25 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (371 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (371 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_371 :
    recurrence4Scalar0Main.coeff 371 =
      -(((((145 * 10 ^ 70 +
        5136983548985616439773869448647781041232238818429159695473345881529601) * 10 ^ 70 +
        1024903065897330975384458409408462582064702879933053826923934935537618) * 10 ^ 70 +
        8435413280491767523977036200422661175579805128168772126257161299985247) * 10 ^ 70 +
        7878876011639211629953047511503783691993486114684204119752264709560389) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (371 - x)) = _
  rw [show 372 = 25 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 24 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (372 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (372 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_372 :
    recurrence4Scalar0Main.coeff 372 =
      (((((59 * 10 ^ 70 +
        1845835697000199566246222650535187560405476487370633737899187346774586) * 10 ^ 70 +
        8172308732227895295135171454862672426866828218672435296729733978545200) * 10 ^ 70 +
        9916592645380503582325475071585150892047650599363340673287661319302020) * 10 ^ 70 +
        2775942522676288804991956347787226724525198345723818694052061006201472) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (372 - x)) = _
  rw [show 373 = 26 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 23 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (373 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (373 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_373 :
    recurrence4Scalar0Main.coeff 373 =
      -(((((23 * 10 ^ 70 +
        3746565372976844637875094509436168818117986771914968483880337807084888) * 10 ^ 70 +
        7090919261192123839033507273248235673388125976801108525363050211944708) * 10 ^ 70 +
        9787589271542753107368963948382817800834421325898614502678634623601190) * 10 ^ 70 +
        5043023440430044446933683818383072050941701202723594443304808350505821) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (373 - x)) = _
  rw [show 374 = 27 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 22 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (374 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (374 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_374 :
    recurrence4Scalar0Main.coeff 374 =
      (((((8 * 10 ^ 70 +
        9526664646167444243456093795719448112889969181972374416246908429726172) * 10 ^ 70 +
        5309230204493360664301737086492283617252918575792206592671007199877425) * 10 ^ 70 +
        7102940207951848717667884668351976336302601438070265126799231468061967) * 10 ^ 70 +
        6758511884035559182820556055399358520607476418044555856382200535699291) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (374 - x)) = _
  rw [show 375 = 28 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 21 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (375 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (375 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_375 :
    recurrence4Scalar0Main.coeff 375 =
      -(((((3 * 10 ^ 70 +
        3198400663202120789430370934551176044939855812247734793882809514044735) * 10 ^ 70 +
        2334985682056750234278811772430545495028000624252436419965484925205217) * 10 ^ 70 +
        6540079805174680815890980832076945568905548618904796070800502579782492) * 10 ^ 70 +
        4955042861466142982009108225285506646445278070392409364209278729678238) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (375 - x)) = _
  rw [show 376 = 29 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 20 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (376 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (376 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_376 :
    recurrence4Scalar0Main.coeff 376 =
      (((((1 * 10 ^ 70 +
        1892389672131221373420889575136431863871924484551316096483870067259501) * 10 ^ 70 +
        2845704385100516050737332072330428467841031828887914226129525916837139) * 10 ^ 70 +
        5414671335338814442466148935622423151963897137085078204882012682626819) * 10 ^ 70 +
        7434775678244587355610457913895226351451073859112205793976952962612390) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (376 - x)) = _
  rw [show 377 = 30 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 19 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (377 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (377 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_377 :
    recurrence4Scalar0Main.coeff 377 =
      -((((4102395532120988597787973335889675844147300720913617804590064372549479 * 10 ^ 70 +
        2350986129453971493003672770607718490729341771283064050267791453738237) * 10 ^ 70 +
        3621737617783246129759292336976214950509724999733962563652809202258136) * 10 ^ 70 +
        1131849130226505121155869106186917345375518737920641984472049870759134) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (377 - x)) = _
  rw [show 378 = 31 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 18 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (378 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (378 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_378 :
    recurrence4Scalar0Main.coeff 378 =
      ((((1356498849236387219643863683408073600916978266096071928183675445804393 * 10 ^ 70 +
        1570606101830412704239632805697314632613374413979466131963695830420768) * 10 ^ 70 +
        2283932716028855790597432547939066193682018495241414123773103189638209) * 10 ^ 70 +
        5190920610274325792856114318426973626037290508943415702625857813471374) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (378 - x)) = _
  rw [show 379 = 32 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 17 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (379 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (379 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_379 :
    recurrence4Scalar0Main.coeff 379 =
      -((((426926479411988371335713978364365155336898909614092662300620419906260 * 10 ^ 70 +
        0260217224011836870322973515729335894825185019568873055078346709861231) * 10 ^ 70 +
        6652286257489920442468680153494932440769233687608996280460895635028051) * 10 ^ 70 +
        5237827171527076305213736865894267401478800258998759930251040722226186) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (379 - x)) = _
  rw [show 380 = 33 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 16 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (380 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (380 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_380 :
    recurrence4Scalar0Main.coeff 380 =
      ((((126425839264600679549290788649364149445025938433354032346775784995028 * 10 ^ 70 +
        3585553372619544856673536925399452707751563740152181405614940274068304) * 10 ^ 70 +
        2679579278821760805328157339740864010260116935056430066175451633184360) * 10 ^ 70 +
        6076632598532073284265036643501545089183328713591903916368725713442824) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (380 - x)) = _
  rw [show 381 = 34 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 15 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (381 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (381 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_381 :
    recurrence4Scalar0Main.coeff 381 =
      -((((34500375115173718255447611419259543872753238813104500157137967819972 * 10 ^ 70 +
        4159200569899468192056769467922287417832412426194950606053006256897303) * 10 ^ 70 +
        5497210532912023737575041964081037378249860077303292525197514695384118) * 10 ^ 70 +
        3551243522259414305429278409743236579561730607347116172923242117589865) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (381 - x)) = _
  rw [show 382 = 35 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 14 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_381_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (382 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (382 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_382 :
    recurrence4Scalar0Main.coeff 382 =
      ((((8300165323055698318497837719642105651547265048953959612392965888536 * 10 ^ 70 +
        1117206982775338532043212479412455632169908377914787162568982290066331) * 10 ^ 70 +
        2851380662904930025291295909540016782670581370842682479572766269243305) * 10 ^ 70 +
        9277694672775719683117702887436594933129400884655880086636695631336037) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (382 - x)) = _
  rw [show 383 = 36 +
    347 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 347 = 32 +
      315 by norm_num, Finset.sum_range_add]
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
    rw [show 219 = 13 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_382_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
