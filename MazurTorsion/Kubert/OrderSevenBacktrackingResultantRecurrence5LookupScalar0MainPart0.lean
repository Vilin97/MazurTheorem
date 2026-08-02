/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B0_coeff_0
  recurrence5B0_coeff_1
  recurrence5B0_coeff_2
  recurrence5B0_coeff_3
  recurrence5B0_coeff_4
  recurrence5B0_coeff_5
  recurrence5B0_coeff_6
  recurrence5B0_coeff_7
  recurrence5B0_coeff_8
  recurrence5B0_coeff_9
  recurrence5B0_coeff_10
  recurrence5B0_coeff_11
  recurrence5B0_coeff_12
  recurrence5B0_coeff_13
  recurrence5B0_coeff_14
  recurrence5B0_coeff_15
  recurrence5B0_coeff_16
  recurrence5B0_coeff_17
  recurrence5B0_coeff_18
  recurrence5B0_coeff_19
  recurrence5B0_coeff_20
  recurrence5B0_coeff_21
  recurrence5B0_coeff_22
  recurrence5B0_coeff_23
  recurrence5B0_coeff_24
  recurrence5B0_coeff_25
  recurrence5B0_coeff_26
  recurrence5B0_coeff_27
  recurrence5B0_coeff_28
  recurrence5B0_coeff_29
  recurrence5B0_coeff_30
  recurrence5B0_coeff_31
  recurrence5B0_coeff_32
  recurrence5B0_coeff_33
  recurrence5B0_coeff_34
  recurrence5B0_coeff_35
  recurrence5B0_coeff_36
  recurrence5B0_coeff_37
  recurrence5B0_coeff_38
  recurrence5B0_coeff_39
  recurrence5B0_coeff_40
  recurrence5B0_coeff_41
  recurrence5B0_coeff_42
  recurrence5B0_coeff_43
  recurrence5B0_coeff_44
  recurrence5B0_coeff_45
  recurrence5B0_coeff_46
  recurrence5B0_coeff_47
  recurrence5B0_coeff_48
  recurrence5B0_coeff_49
  recurrence5B0_coeff_50
  recurrence5B0_coeff_51
  recurrence5B0_coeff_52
  recurrence5B0_coeff_53
  recurrence5B0_coeff_54
  recurrence5B0_coeff_55
  recurrence5B0_coeff_56
  recurrence5B0_coeff_57
  recurrence5B0_coeff_58
  recurrence5B0_coeff_59
  recurrence5B0_coeff_60
  recurrence5B0_coeff_61
  recurrence5B0_coeff_62
  recurrence5B0_coeff_63

attribute [local simp]
  recurrence5B0_coeff_64
  recurrence5B0_coeff_65
  recurrence5B0_coeff_66
  recurrence5B0_coeff_67
  recurrence5B0_coeff_68
  recurrence5B0_coeff_69
  recurrence5B0_coeff_70
  recurrence5B0_coeff_71
  recurrence5B0_coeff_72
  recurrence5B0_coeff_73
  recurrence5B0_coeff_74
  recurrence5B0_coeff_75
  recurrence5B0_coeff_76
  recurrence5B0_coeff_77
  recurrence5B0_coeff_78
  recurrence5B0_coeff_79
  recurrence5B0_coeff_80
  recurrence5B0_coeff_81
  recurrence5B0_coeff_82
  recurrence5B0_coeff_83
  recurrence5B0_coeff_84
  recurrence5B0_coeff_85
  recurrence5B0_coeff_86
  recurrence5B0_coeff_87
  recurrence5B0_coeff_88
  recurrence5B0_coeff_89
  recurrence5B0_coeff_90
  recurrence5B0_coeff_91
  recurrence5B0_coeff_92
  recurrence5B0_coeff_93
  recurrence5B0_coeff_94
  recurrence5B0_coeff_95
  recurrence5B0_coeff_96
  recurrence5B0_coeff_97
  recurrence5B0_coeff_98
  recurrence5B0_coeff_99
  recurrence5B0_coeff_100
  recurrence5B0_coeff_101
  recurrence5B0_coeff_102
  recurrence5B0_coeff_103
  recurrence5B0_coeff_104
  recurrence5B0_coeff_105
  recurrence5B0_coeff_106
  recurrence5B0_coeff_107
  recurrence5B0_coeff_108
  recurrence5B0_coeff_109
  recurrence5B0_coeff_110
  recurrence5B0_coeff_111
  recurrence5B0_coeff_112
  recurrence5B0_coeff_113
  recurrence5B0_coeff_114
  recurrence5B0_coeff_115
  recurrence5B0_coeff_116
  recurrence5B0_coeff_117
  recurrence5B0_coeff_118
  recurrence5B0_coeff_119
  recurrence5B0_coeff_120
  recurrence5B0_coeff_121
  recurrence5B0_coeff_122
  recurrence5B0_coeff_123
  recurrence5B0_coeff_124
  recurrence5B0_coeff_125
  recurrence5B0_coeff_126
  recurrence5B0_coeff_127

attribute [local simp]
  recurrence5B0_coeff_128
  recurrence5B0_coeff_129
  recurrence5B0_coeff_130
  recurrence5B0_coeff_131
  recurrence5B0_coeff_132
  recurrence5B0_coeff_133
  recurrence5B0_coeff_134
  recurrence5B0_coeff_135
  recurrence5B0_coeff_136
  recurrence5B0_coeff_137
  recurrence5B0_coeff_138
  recurrence5B0_coeff_139
  recurrence5B0_coeff_140
  recurrence5B0_coeff_141
  recurrence5B0_coeff_142
  recurrence5B0_coeff_143
  recurrence5B0_coeff_144
  recurrence5B0_coeff_145
  recurrence5B0_coeff_146
  recurrence5B0_coeff_147
  recurrence5B0_coeff_148
  recurrence5B0_coeff_149
  recurrence5B0_coeff_150
  recurrence5B0_coeff_151
  recurrence5B0_coeff_152
  recurrence5B0_coeff_153
  recurrence5QuotientConstant_coeff_0
  recurrence5QuotientConstant_coeff_1
  recurrence5QuotientConstant_coeff_2
  recurrence5QuotientConstant_coeff_3
  recurrence5QuotientConstant_coeff_4
  recurrence5QuotientConstant_coeff_5
  recurrence5QuotientConstant_coeff_6
  recurrence5QuotientConstant_coeff_7
  recurrence5QuotientConstant_coeff_8
  recurrence5QuotientConstant_coeff_9
  recurrence5QuotientConstant_coeff_10
  recurrence5QuotientConstant_coeff_11
  recurrence5QuotientConstant_coeff_12
  recurrence5QuotientConstant_coeff_13
  recurrence5QuotientConstant_coeff_14
  recurrence5QuotientConstant_coeff_15
  recurrence5QuotientConstant_coeff_16
  recurrence5QuotientConstant_coeff_17
  recurrence5QuotientConstant_coeff_18
  recurrence5QuotientConstant_coeff_19
  recurrence5QuotientConstant_coeff_20
  recurrence5QuotientConstant_coeff_21
  recurrence5QuotientConstant_coeff_22
  recurrence5QuotientConstant_coeff_23
  recurrence5QuotientConstant_coeff_24
  recurrence5QuotientConstant_coeff_25
  recurrence5QuotientConstant_coeff_26
  recurrence5QuotientConstant_coeff_27
  recurrence5QuotientConstant_coeff_28
  recurrence5QuotientConstant_coeff_29
  recurrence5QuotientConstant_coeff_30
  recurrence5QuotientConstant_coeff_31
  recurrence5QuotientConstant_coeff_32
  recurrence5QuotientConstant_coeff_33
  recurrence5QuotientConstant_coeff_34
  recurrence5QuotientConstant_coeff_35
  recurrence5QuotientConstant_coeff_36
  recurrence5QuotientConstant_coeff_37

attribute [local simp]
  recurrence5QuotientConstant_coeff_38
  recurrence5QuotientConstant_coeff_39
  recurrence5QuotientConstant_coeff_40
  recurrence5QuotientConstant_coeff_41
  recurrence5QuotientConstant_coeff_42
  recurrence5QuotientConstant_coeff_43
  recurrence5QuotientConstant_coeff_44
  recurrence5QuotientConstant_coeff_45
  recurrence5QuotientConstant_coeff_46
  recurrence5QuotientConstant_coeff_47
  recurrence5QuotientConstant_coeff_48
  recurrence5QuotientConstant_coeff_49
  recurrence5QuotientConstant_coeff_50
  recurrence5QuotientConstant_coeff_51
  recurrence5QuotientConstant_coeff_52
  recurrence5QuotientConstant_coeff_53
  recurrence5QuotientConstant_coeff_54
  recurrence5QuotientConstant_coeff_55
  recurrence5QuotientConstant_coeff_56
  recurrence5QuotientConstant_coeff_57
  recurrence5QuotientConstant_coeff_58
  recurrence5QuotientConstant_coeff_59
  recurrence5QuotientConstant_coeff_60
  recurrence5QuotientConstant_coeff_61
  recurrence5QuotientConstant_coeff_62
  recurrence5QuotientConstant_coeff_63
  recurrence5QuotientConstant_coeff_64
  recurrence5QuotientConstant_coeff_65
  recurrence5QuotientConstant_coeff_66
  recurrence5QuotientConstant_coeff_67
  recurrence5QuotientConstant_coeff_68
  recurrence5QuotientConstant_coeff_69
  recurrence5QuotientConstant_coeff_70
  recurrence5QuotientConstant_coeff_71
  recurrence5QuotientConstant_coeff_72
  recurrence5QuotientConstant_coeff_73
  recurrence5QuotientConstant_coeff_74
  recurrence5QuotientConstant_coeff_75
  recurrence5QuotientConstant_coeff_76
  recurrence5QuotientConstant_coeff_77
  recurrence5QuotientConstant_coeff_78
  recurrence5QuotientConstant_coeff_79
  recurrence5QuotientConstant_coeff_80
  recurrence5QuotientConstant_coeff_81
  recurrence5QuotientConstant_coeff_82
  recurrence5QuotientConstant_coeff_83
  recurrence5QuotientConstant_coeff_84
  recurrence5QuotientConstant_coeff_85
  recurrence5QuotientConstant_coeff_86
  recurrence5QuotientConstant_coeff_87
  recurrence5QuotientConstant_coeff_88
  recurrence5QuotientConstant_coeff_89
  recurrence5QuotientConstant_coeff_90
  recurrence5QuotientConstant_coeff_91
  recurrence5QuotientConstant_coeff_92
  recurrence5QuotientConstant_coeff_93
  recurrence5QuotientConstant_coeff_94
  recurrence5QuotientConstant_coeff_95
  recurrence5QuotientConstant_coeff_96
  recurrence5QuotientConstant_coeff_97
  recurrence5QuotientConstant_coeff_98
  recurrence5QuotientConstant_coeff_99
  recurrence5QuotientConstant_coeff_100
  recurrence5QuotientConstant_coeff_101

attribute [local simp]
  recurrence5QuotientConstant_coeff_102
  recurrence5QuotientConstant_coeff_103
  recurrence5QuotientConstant_coeff_104
  recurrence5QuotientConstant_coeff_105
  recurrence5QuotientConstant_coeff_106
  recurrence5QuotientConstant_coeff_107
  recurrence5QuotientConstant_coeff_108
  recurrence5QuotientConstant_coeff_109
  recurrence5QuotientConstant_coeff_110
  recurrence5QuotientConstant_coeff_111
  recurrence5QuotientConstant_coeff_112
  recurrence5QuotientConstant_coeff_113
  recurrence5QuotientConstant_coeff_114
  recurrence5QuotientConstant_coeff_115
  recurrence5QuotientConstant_coeff_116
  recurrence5QuotientConstant_coeff_117
  recurrence5QuotientConstant_coeff_118
  recurrence5QuotientConstant_coeff_119
  recurrence5QuotientConstant_coeff_120
  recurrence5QuotientConstant_coeff_121
  recurrence5QuotientConstant_coeff_122
  recurrence5QuotientConstant_coeff_123
  recurrence5QuotientConstant_coeff_124
  recurrence5QuotientConstant_coeff_125
  recurrence5QuotientConstant_coeff_126
  recurrence5QuotientConstant_coeff_127
  recurrence5QuotientConstant_coeff_128
  recurrence5QuotientConstant_coeff_129
  recurrence5QuotientConstant_coeff_130
  recurrence5QuotientConstant_coeff_131
  recurrence5QuotientConstant_coeff_132
  recurrence5QuotientConstant_coeff_133
  recurrence5QuotientConstant_coeff_134
  recurrence5QuotientConstant_coeff_135
  recurrence5QuotientConstant_coeff_136
  recurrence5QuotientConstant_coeff_137
  recurrence5QuotientConstant_coeff_138
  recurrence5QuotientConstant_coeff_139
  recurrence5QuotientConstant_coeff_140
  recurrence5QuotientConstant_coeff_141
  recurrence5QuotientConstant_coeff_142
  recurrence5QuotientConstant_coeff_143
  recurrence5QuotientConstant_coeff_144
  recurrence5QuotientConstant_coeff_145
  recurrence5QuotientConstant_coeff_146
  recurrence5QuotientConstant_coeff_147
  recurrence5QuotientConstant_coeff_148
  recurrence5QuotientConstant_coeff_149
  recurrence5QuotientConstant_coeff_150
  recurrence5QuotientConstant_coeff_151
  recurrence5QuotientConstant_coeff_152
  recurrence5QuotientConstant_coeff_153
  recurrence5QuotientConstant_coeff_154
  recurrence5QuotientConstant_coeff_155
  recurrence5QuotientConstant_coeff_156
  recurrence5QuotientConstant_coeff_157
  recurrence5QuotientConstant_coeff_158
  recurrence5QuotientConstant_coeff_159
  recurrence5QuotientConstant_coeff_160
  recurrence5QuotientConstant_coeff_161
  recurrence5QuotientConstant_coeff_162
  recurrence5QuotientConstant_coeff_163
  recurrence5QuotientConstant_coeff_164
  recurrence5QuotientConstant_coeff_165

attribute [local simp]
  recurrence5QuotientConstant_coeff_166
  recurrence5QuotientConstant_coeff_167
  recurrence5QuotientConstant_coeff_168
  recurrence5QuotientConstant_coeff_169
  recurrence5QuotientConstant_coeff_170
  recurrence5QuotientConstant_coeff_171
  recurrence5QuotientConstant_coeff_172
  recurrence5QuotientConstant_coeff_173
  recurrence5QuotientConstant_coeff_174
  recurrence5QuotientConstant_coeff_175
  recurrence5QuotientConstant_coeff_176
  recurrence5QuotientConstant_coeff_177
  recurrence5QuotientConstant_coeff_178
  recurrence5QuotientConstant_coeff_179
  recurrence5QuotientConstant_coeff_180
  recurrence5QuotientConstant_coeff_181
  recurrence5QuotientConstant_coeff_182
  recurrence5QuotientConstant_coeff_183
  recurrence5QuotientConstant_coeff_184
  recurrence5QuotientConstant_coeff_185
  recurrence5QuotientConstant_coeff_186
  recurrence5QuotientConstant_coeff_187
  recurrence5QuotientConstant_coeff_188
  recurrence5QuotientConstant_coeff_189
  recurrence5QuotientConstant_coeff_190
  recurrence5QuotientConstant_coeff_191
  recurrence5QuotientConstant_coeff_192
  recurrence5QuotientConstant_coeff_193
  recurrence5QuotientConstant_coeff_194
  recurrence5QuotientConstant_coeff_195
  recurrence5QuotientConstant_coeff_196
  recurrence5QuotientConstant_coeff_197
  recurrence5QuotientConstant_coeff_198
  recurrence5QuotientConstant_coeff_199
  recurrence5QuotientConstant_coeff_200
  recurrence5QuotientConstant_coeff_201
  recurrence5QuotientConstant_coeff_202
  recurrence5QuotientConstant_coeff_203
  recurrence5QuotientConstant_coeff_204
  recurrence5QuotientConstant_coeff_205
  recurrence5QuotientConstant_coeff_206
  recurrence5QuotientConstant_coeff_207
  recurrence5QuotientConstant_coeff_208
  recurrence5QuotientConstant_coeff_209
  recurrence5QuotientConstant_coeff_210
  recurrence5QuotientConstant_coeff_211
  recurrence5QuotientConstant_coeff_212
  recurrence5QuotientConstant_coeff_213
  recurrence5QuotientConstant_coeff_214
  recurrence5QuotientConstant_coeff_215
  recurrence5QuotientConstant_coeff_216
  recurrence5QuotientConstant_coeff_217
  recurrence5QuotientConstant_coeff_218
  recurrence5QuotientConstant_coeff_219
  recurrence5QuotientConstant_coeff_220
  recurrence5QuotientConstant_coeff_221
  recurrence5QuotientConstant_coeff_222
  recurrence5QuotientConstant_coeff_223
  recurrence5QuotientConstant_coeff_224
  recurrence5QuotientConstant_coeff_225
  recurrence5QuotientConstant_coeff_226
  recurrence5QuotientConstant_coeff_227
  recurrence5QuotientConstant_coeff_228
  recurrence5QuotientConstant_coeff_229

attribute [local simp]
  recurrence5QuotientConstant_coeff_230
  recurrence5QuotientConstant_coeff_231
  recurrence5QuotientConstant_coeff_232
  recurrence5QuotientConstant_coeff_233
  recurrence5QuotientConstant_coeff_234
  recurrence5QuotientConstant_coeff_235
  recurrence5QuotientConstant_coeff_236
  recurrence5QuotientConstant_coeff_237
  recurrence5QuotientConstant_coeff_238
  recurrence5QuotientConstant_coeff_239
  recurrence5QuotientConstant_coeff_240
  recurrence5QuotientConstant_coeff_241
  recurrence5QuotientConstant_coeff_242
  recurrence5QuotientConstant_coeff_243
  recurrence5QuotientConstant_coeff_244
  recurrence5QuotientConstant_coeff_245
  recurrence5QuotientConstant_coeff_246
  recurrence5QuotientConstant_coeff_247
  recurrence5QuotientConstant_coeff_248
  recurrence5QuotientConstant_coeff_249
  recurrence5QuotientConstant_coeff_250
  recurrence5QuotientConstant_coeff_251
  recurrence5QuotientConstant_coeff_252
  recurrence5QuotientConstant_coeff_253
  recurrence5QuotientConstant_coeff_254
  recurrence5QuotientConstant_coeff_255
  recurrence5QuotientConstant_coeff_256
  recurrence5QuotientConstant_coeff_257
  recurrence5QuotientConstant_coeff_258
  recurrence5QuotientConstant_coeff_259
  recurrence5QuotientConstant_coeff_260
  recurrence5QuotientConstant_coeff_261
  recurrence5QuotientConstant_coeff_262
  recurrence5QuotientConstant_coeff_263
  recurrence5QuotientConstant_coeff_264
  recurrence5QuotientConstant_coeff_265
  recurrence5QuotientConstant_coeff_266
  recurrence5QuotientConstant_coeff_267
  recurrence5QuotientConstant_coeff_268
  recurrence5QuotientConstant_coeff_269
  recurrence5QuotientConstant_coeff_270
  recurrence5QuotientConstant_coeff_271
  recurrence5QuotientConstant_coeff_272
  recurrence5QuotientConstant_coeff_273
  recurrence5QuotientConstant_coeff_274
  recurrence5QuotientConstant_coeff_275
  recurrence5QuotientConstant_coeff_276
  recurrence5QuotientConstant_coeff_277
  recurrence5QuotientConstant_coeff_278
  recurrence5QuotientConstant_coeff_279
  recurrence5QuotientConstant_coeff_280
  recurrence5QuotientConstant_coeff_281
  recurrence5QuotientConstant_coeff_282
  recurrence5QuotientConstant_coeff_283
  recurrence5QuotientConstant_coeff_284
  recurrence5QuotientConstant_coeff_285
  recurrence5QuotientConstant_coeff_286
  recurrence5QuotientConstant_coeff_287
  recurrence5QuotientConstant_coeff_288
  recurrence5QuotientConstant_coeff_289
  recurrence5QuotientConstant_coeff_290
  recurrence5QuotientConstant_coeff_291
  recurrence5QuotientConstant_coeff_292
  recurrence5QuotientConstant_coeff_293

attribute [local simp]
  recurrence5QuotientConstant_coeff_294
  recurrence5QuotientConstant_coeff_295
  recurrence5QuotientConstant_coeff_296
  recurrence5QuotientConstant_coeff_297
  recurrence5QuotientConstant_coeff_298
  recurrence5QuotientConstant_coeff_299
  recurrence5QuotientConstant_coeff_300
  recurrence5QuotientConstant_coeff_301
  recurrence5QuotientConstant_coeff_302
  recurrence5QuotientConstant_coeff_303
  recurrence5QuotientConstant_coeff_304
  recurrence5QuotientConstant_coeff_305
  recurrence5QuotientConstant_coeff_306
  recurrence5QuotientConstant_coeff_307
  recurrence5QuotientConstant_coeff_308
  recurrence5QuotientConstant_coeff_309
  recurrence5QuotientConstant_coeff_310
  recurrence5QuotientConstant_coeff_311
  recurrence5QuotientConstant_coeff_312
  recurrence5QuotientConstant_coeff_313

theorem recurrence5Scalar0Main_coeff_0 :
    recurrence5Scalar0Main.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_1 :
    recurrence5Scalar0Main.coeff 1 =
      ((57838809210387311374847545185027900089879989385612125 * 10 ^ 70 +
        6384469871949651332869024275032357497219488186425400442200125916446720) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_2 :
    recurrence5Scalar0Main.coeff 2 =
      ((323141313941434388461168111861766606385314873727581536340 * 10 ^ 70 +
        2115917639077005777857077396306872046623187316883489469228549258682368) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_3 :
    recurrence5Scalar0Main.coeff 3 =
      -((2532364183808920979027641238568235521235338235888259839279002 * 10 ^ 70 +
        8132869705089289876393383163511610062433670164994999589633615798896128) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_4 :
    recurrence5Scalar0Main.coeff 4 =
      ((292010068263915887983879214604469968115971693895915544969288598 * 10 ^ 70 +
        7282571757943099679616349397388397815470941928927209575630277621713856) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_5 :
    recurrence5Scalar0Main.coeff 5 =
      ((21837674225547188417642625427236224912882897134563390754353941664893 * 10 ^ 70 +
        2190621952803799309065034090547418408356419084568486306100123749240960) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_6 :
    recurrence5Scalar0Main.coeff 6 =
      -(((8 * 10 ^ 70 +
        8392734215249432259986419020159408121979319591703867405668337206071713) * 10 ^ 70 +
        9898500117100359138918722235694096799172211253767219857768857512153584) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_7 :
    recurrence5Scalar0Main.coeff 7 =
      (((21387 * 10 ^ 70 +
        6897561152310288911195276436497449822822458010232441973215101320416949) * 10 ^ 70 +
        4259285939754687426445161820732945456385611926457032716980749227191072) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_8 :
    recurrence5Scalar0Main.coeff 8 =
      -(((35780448 * 10 ^ 70 +
        5356355545866072176485233101388623065716501334138613636985239935378452) * 10 ^ 70 +
        1058856198272806049405612978664103645426835400305667206817843666036624) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_9 :
    recurrence5Scalar0Main.coeff 9 =
      (((44577167544 * 10 ^ 70 +
        2170775662776891439339282542712338966634310124108279863197753126702285) * 10 ^ 70 +
        8218558740186322994977924605626481395418677009612977096830527218090416) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_10 :
    recurrence5Scalar0Main.coeff 10 =
      -(((41221330744690 * 10 ^ 70 +
        4521696510404507151443379824966063545016773116643147645962223942227029) * 10 ^ 70 +
        9514316667884425643084633608213507628306289184228259655718038295992512) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_11 :
    recurrence5Scalar0Main.coeff 11 =
      (((26242491675423200 * 10 ^ 70 +
        1972428293357447415977155280227579748172533498175782627588295603821271) * 10 ^ 70 +
        8486971930702271887848693029029043516525970115600403331120565955978884) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_12 :
    recurrence5Scalar0Main.coeff 12 =
      -(((8288369343204197333 * 10 ^ 70 +
        3850010871843817857526114240153591243056643516558576899358795105496692) * 10 ^ 70 +
        3716242138050422303305072430822858048639053764686222019370467168282624) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_13 :
    recurrence5Scalar0Main.coeff 13 =
      -(((3404978826691946689189 * 10 ^ 70 +
        5667593329672353891070161208698226595714453532238603869461201008884208) * 10 ^ 70 +
        0780880173050052502423577396674288303944712797252084712755217987339440) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_14 :
    recurrence5Scalar0Main.coeff 14 =
      (((6423030090510165891971557 * 10 ^ 70 +
        5539401842725889510355143536327292591288054492826006195564197335124924) * 10 ^ 70 +
        0450256549530353023050625935225593873710668028433357597637256149836588) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_15 :
    recurrence5Scalar0Main.coeff 15 =
      -(((4425831551956719263561837709 * 10 ^ 70 +
        3624213891211084711329197103033063969243727231664893412253996026617667) * 10 ^ 70 +
        7458848808368374706470654525551194910598597105624306492834964840494460) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_16 :
    recurrence5Scalar0Main.coeff 16 =
      (((1746526359240885793209389485945 * 10 ^ 70 +
        3588510912078879748524094098581923148570222363295699378758781788907873) * 10 ^ 70 +
        2238907079231904728580335426846153561022746448849150205083035421704620) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_17 :
    recurrence5Scalar0Main.coeff 17 =
      -(((258528613776133376008274695311100 * 10 ^ 70 +
        6777805933044912775732371968183901741602639336912168726823370762410822) * 10 ^ 70 +
        6970922440184055872184865227188034702566965779589298900886652778236428) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_18 :
    recurrence5Scalar0Main.coeff 18 =
      -(((161829115797770083933000393563750661 * 10 ^ 70 +
        3525417201031714455261274815254128349804261835229254241797989501806201) * 10 ^ 70 +
        6658411495701051073089471586520666676442339664045595470800394774519200) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_19 :
    recurrence5Scalar0Main.coeff 19 =
      (((142189019980987675545075798705683377379 * 10 ^ 70 +
        9822611039237380354942431501165276291219012254337597986970856362729142) * 10 ^ 70 +
        0802685711807367288373510454341642280664844701001201110610435514951236) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_20 :
    recurrence5Scalar0Main.coeff 20 =
      -(((60056791412543562067615713677327294618256 * 10 ^ 70 +
        1790471149162578418729255024866136312593571894323213590708340858123359) * 10 ^ 70 +
        0322874336100932636593567996453025450726137064317658958906924539274984) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_21 :
    recurrence5Scalar0Main.coeff 21 =
      (((16519024191561087072760524767339222740382035 * 10 ^ 70 +
        9736389176221329532264600234100817195553115175435630477625320886028387) * 10 ^ 70 +
        1800030872351961611844707673337627141712547083676479898410538094396373) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_22 :
    recurrence5Scalar0Main.coeff 22 =
      -(((3325404342623622378762293137875376482150673419 * 10 ^ 70 +
        1790085454714974961087414574277487598668656064328649833274251353246791) * 10 ^ 70 +
        1059480463876304563214102550959285241205817792557635595498259928552408) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_23 :
    recurrence5Scalar0Main.coeff 23 =
      (((933995559748540271466456427806949321052833965426 * 10 ^ 70 +
        4996831637306773464136979083127587837147701094452788151073386999902454) * 10 ^ 70 +
        0779167147589956257892929461500573892274332445412247329617519052660706) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_24 :
    recurrence5Scalar0Main.coeff 24 =
      -(((609423785603187813444468989899985659725087603929320 * 10 ^ 70 +
        8919245582825291089658003833629128597062544572857034696450669897030083) * 10 ^ 70 +
        7463300035467275475539327136802236582941985600458088854977694914715624) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_25 :
    recurrence5Scalar0Main.coeff 25 =
      (((390111683730161048656186163180461447591727733249345703 * 10 ^ 70 +
        1813440664523106554798472752078029352583417282939884768283605300594986) * 10 ^ 70 +
        4937957687213358504124783571223103313105963279745500399788223316295180) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_26 :
    recurrence5Scalar0Main.coeff 26 =
      -(((190481937455917319729339914792386240023639094671316542251 * 10 ^ 70 +
        7202467810447501050621564336499248125791213574006074955131862599767045) * 10 ^ 70 +
        1064606159929552413415621812250064800039630288818928156131932497499077) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_27 :
    recurrence5Scalar0Main.coeff 27 =
      (((73373998933777807970795481318486708688344207242000554307865 * 10 ^ 70 +
        2738523427981026206266787512444990718798270417149406544666904579889834) * 10 ^ 70 +
        5714365651358619339310694576571181681564328111270272280841703646492824) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_28 :
    recurrence5Scalar0Main.coeff 28 =
      -(((23249067905309688727590940567702585850915841757492886405839109 * 10 ^ 70 +
        5874542900815439227467747729122123584838255294175887339426176519729337) * 10 ^ 70 +
        2364101285299899889935890909175585786615332438346794715198707185702426) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_29 :
    recurrence5Scalar0Main.coeff 29 =
      (((6226837867259704077304319831012451430024994324691629921997118041 * 10 ^ 70 +
        2131809118912579853598052493735007062124890780622730678741191843937467) * 10 ^ 70 +
        5612638239225680891563512144173223862942743122481738805002350690198656) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_30 :
    recurrence5Scalar0Main.coeff 30 =
      -(((1432492759438965526997163709862150963034818598849873079575710354610 * 10 ^ 70 +
        6133999875960558645655302258773719503191293106873944688383027139357523) * 10 ^ 70 +
        8920494392021597308091126312540307405975047724051466503220700072753432) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_31 :
    recurrence5Scalar0Main.coeff 31 =
      (((285250058307926429888441413354004206310641676206343719538346894558615 * 10 ^ 70 +
        5834357829845204728326806032513134068358840178063705488485121403095579) * 10 ^ 70 +
        2180792132968237899394187706719047996376988874905704472270110531039033) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_32 :
    recurrence5Scalar0Main.coeff 32 =
      -((((4 * 10 ^ 70 +
        9155788576328057912754888255214400755015014446622498101586425346187572) * 10 ^ 70 +
        7540346599419549820805133902827676758071751389491199325843262028574803) * 10 ^ 70 +
        1663993495333970098033534214523714762613374528381565851368897628862413) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_33 :
    recurrence5Scalar0Main.coeff 33 =
      ((((724 * 10 ^ 70 +
        9154182127296298647098608866865601825926040332357382495922426453953493) * 10 ^ 70 +
        1804761351551206792439106002283961211111014636011703521790625267788020) * 10 ^ 70 +
        3531218043049381940955903736925218288556067593325972607190496144471508) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_34 :
    recurrence5Scalar0Main.coeff 34 =
      -((((88449 * 10 ^ 70 +
        6944111811646468774492196744005922596495820086189899369420155995189987) * 10 ^ 70 +
        1318118682990108916964809374816431960192807828373350343949674965948232) * 10 ^ 70 +
        6165740830476756977282526819172099908261650042634178747340272272215485) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_35 :
    recurrence5Scalar0Main.coeff 35 =
      ((((8036384 * 10 ^ 70 +
        0673152261508763875059233726423918631402382026012087906188027306020137) * 10 ^ 70 +
        4082652415062338739026060100675237318727972731561407122775518066347777) * 10 ^ 70 +
        4975758631866178562471682060108089231717754847294330168243451489631611) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_36 :
    recurrence5Scalar0Main.coeff 36 =
      -((((285831349 * 10 ^ 70 +
        8788392089722687718697873791585415188711480246159223933606186104454050) * 10 ^ 70 +
        8163348949120704491043781159748610595245234387123677598203380925546831) * 10 ^ 70 +
        6451550986230563320343309868180690412989328117612271199506229753723881) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_37 :
    recurrence5Scalar0Main.coeff 37 =
      -((((82043957794 * 10 ^ 70 +
        0174523200254891667768771226663235327791936972984495899111558639400407) * 10 ^ 70 +
        4684741203981032993148441286050425859655688704636985135199161885655764) * 10 ^ 70 +
        6294149150436196039662406112420776312575721867632277215881722246486895) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_38 :
    recurrence5Scalar0Main.coeff 38 =
      ((((25339298658919 * 10 ^ 70 +
        1251739956349009463467891418369455020788412570592268658296120085971095) * 10 ^ 70 +
        5567824471628830948863523955267849830378625599476008821273759720864501) * 10 ^ 70 +
        9930190256327336779455015529169942032873255478643478790982216612229959) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_39 :
    recurrence5Scalar0Main.coeff 39 =
      -((((4684729676141954 * 10 ^ 70 +
        3985978326752581093206235413966390168644895753693825602486561179640338) * 10 ^ 70 +
        0420250262004041945957198901192894046682236510485189842850249814012576) * 10 ^ 70 +
        0322861989570622256753063792451616281412475038257774245503364152709592) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_40 :
    recurrence5Scalar0Main.coeff 40 =
      ((((692916562412693488 * 10 ^ 70 +
        9633287926043070860371335913006380482188469082588365543798573172422844) * 10 ^ 70 +
        2282164429236293840223150253625346440359474748234693381838979802176432) * 10 ^ 70 +
        4313508506171537928119521743202477438323196208481991334133806954065236) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_41 :
    recurrence5Scalar0Main.coeff 41 =
      -((((88418631201678503772 * 10 ^ 70 +
        5192894855012598466048367550615500484947788785135669967304591728901731) * 10 ^ 70 +
        6544106969809953388389668242924908816130587412365977526117764240816335) * 10 ^ 70 +
        9848740842255750977582997084476689706597863528887046949430879306955226) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_42 :
    recurrence5Scalar0Main.coeff 42 =
      ((((10049925521397056578212 * 10 ^ 70 +
        9252599672697944121214934038600568439369291001679743765954584277667338) * 10 ^ 70 +
        5592956315365184074093240800635354382825688675244342954970781386495519) * 10 ^ 70 +
        3794766004735810431704055698200999253074407119964324378869823765541406) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_43 :
    recurrence5Scalar0Main.coeff 43 =
      -((((1035033448187084566777779 * 10 ^ 70 +
        8111832053579822391423636086500347373346401081186316573886408084286053) * 10 ^ 70 +
        0585423574160226475612621660962462371210173634752828172423587459435953) * 10 ^ 70 +
        1276483641752485637009691288004669764061469648565936379379217364690407) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_44 :
    recurrence5Scalar0Main.coeff 44 =
      ((((97606923113876264791092390 * 10 ^ 70 +
        8800772616538480359774331023553751584769140842573761301451392658137743) * 10 ^ 70 +
        6108963526362860022095702575364268248404951824086166537056038244862182) * 10 ^ 70 +
        2505919199645949013716175897570221961919947942900858887704077533277089) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_45 :
    recurrence5Scalar0Main.coeff 45 =
      -((((8488572060692059052325299834 * 10 ^ 70 +
        6987272101502879053820278096770083204887925537438189698076472109290843) * 10 ^ 70 +
        7448741099801161925904249248623977566602816575271256874551350342882432) * 10 ^ 70 +
        8416476875742930701407248539663968907188538782018458126501403293723594) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_46 :
    recurrence5Scalar0Main.coeff 46 =
      ((((684332575325332431390071346137 * 10 ^ 70 +
        6346844309291167648130031370140540439020721819832037469991096506921304) * 10 ^ 70 +
        9130948968987465707767010071548719909286233087310199708826246499123420) * 10 ^ 70 +
        7703657025794972484047486262091022702039422736248031383415601750503299) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_47 :
    recurrence5Scalar0Main.coeff 47 =
      -((((51345877923166246482737583854255 * 10 ^ 70 +
        0400283343856002550115881897351327557479439862657013576964530836045978) * 10 ^ 70 +
        7994623868556820588665993330426025335108023666871405657241551355122665) * 10 ^ 70 +
        9852354563659179812864685427546922061915588105237122646644343616797428) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_48 :
    recurrence5Scalar0Main.coeff 48 =
      ((((3596914923775274094897247449935879 * 10 ^ 70 +
        7836582600103037018620384056455224070048590472103761873221578370367414) * 10 ^ 70 +
        3530773312859915278981079979958597363717191127802868884492438851747737) * 10 ^ 70 +
        0037906823188277644366348068816358067036692630847398243950812880813039) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_49 :
    recurrence5Scalar0Main.coeff 49 =
      -((((235873549085921761198967550744680166 * 10 ^ 70 +
        2233773131413757646210052884793664496548105313249210543422908822956668) * 10 ^ 70 +
        6820157722607736727091691552465202207670907295223109868133394329931944) * 10 ^ 70 +
        9880381775529913063333548682996991326306919632969653494166816531672178) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_50 :
    recurrence5Scalar0Main.coeff 50 =
      ((((14511567178555322887268822575983837288 * 10 ^ 70 +
        9782369949285148009515614153198423626967358247578985575889360952185921) * 10 ^ 70 +
        1674387945719937752901073947886211884602132130345037755815530034326163) * 10 ^ 70 +
        7662270233086549629599750075343737039691304810101463911583296152426935) : ℚ) := by
  unfold recurrence5Scalar0Main
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

theorem recurrence5Scalar0Main_coeff_51 :
    recurrence5Scalar0Main.coeff 51 =
      -((((839194510205225191779617716653829281435 * 10 ^ 70 +
        2823324251331151407073496988437926646825029921674462764431408731752745) * 10 ^ 70 +
        5576772653649189698178699451432977645034398012056708340309733884427643) * 10 ^ 70 +
        0477268660460955283438843801949648095178216605953217089323211930081357) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_52 :
    recurrence5Scalar0Main.coeff 52 =
      ((((45692584556161050574547304124527362932882 * 10 ^ 70 +
        6666242614304252765530432761362822291911651216227838012568904610056656) * 10 ^ 70 +
        1741625427340594609483599339330113241799685298574845352386535129769481) * 10 ^ 70 +
        6940348550696172529157119580881428711819352381757598512237326550836691) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_53 :
    recurrence5Scalar0Main.coeff 53 =
      -((((2345843279362411060424537833632751795986185 * 10 ^ 70 +
        4384399374121507191711307642484332142444199838612410873239127951612733) * 10 ^ 70 +
        8655269622402782273760197645876836535409858677241276652570640980726881) * 10 ^ 70 +
        0014481815215061113713625177449297588530634999904565634392746177902381) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_54 :
    recurrence5Scalar0Main.coeff 54 =
      ((((113706504773703905756690842071426560492987826 * 10 ^ 70 +
        2581156535538685983679803002980129492337800234177069517452887651190383) * 10 ^ 70 +
        3527257112185122699176147051007916214248175105333631576738401532562221) * 10 ^ 70 +
        6788103437580573747433490680233834119305455372086611675612087987133500) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_55 :
    recurrence5Scalar0Main.coeff 55 =
      -((((5209599456571703205124647004680903668947602251 * 10 ^ 70 +
        1386562663799872696849940650468621340735076496879421731922552169680427) * 10 ^ 70 +
        2716094793666721089057733032021109524065331777185889896451454014652886) * 10 ^ 70 +
        0506968067380071338031333880873477207893184521723094621805195574753772) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_56 :
    recurrence5Scalar0Main.coeff 56 =
      ((((225838874812522888933790251209322747709103842248 * 10 ^ 70 +
        7551453313780347008314615434255452110225867333969447069272962130002896) * 10 ^ 70 +
        1309472794797485878700751653658950341567190226958255056850897268720719) * 10 ^ 70 +
        0568341172026569619325741562239178070795515321012766244716552868484321) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_57 :
    recurrence5Scalar0Main.coeff 57 =
      -((((9271663391332254129577448067720521708957490816726 * 10 ^ 70 +
        7934340759192020142058665064263162329755740410841849828615601165520680) * 10 ^ 70 +
        2566696680349337359758696978109971885476700885107821732364704539648931) * 10 ^ 70 +
        2730507315512361757692330800387973027356871497825145471278436871034353) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_58 :
    recurrence5Scalar0Main.coeff 58 =
      ((((360760059457303110545414666355892507180475568686046 * 10 ^ 70 +
        3854757389777274450429396573560990294155820468711149929764281841311611) * 10 ^ 70 +
        0200966640809734035039910221398814775949251170838454441641429008203155) * 10 ^ 70 +
        4398480623363784631597824179324184831451649577923015593345353316520425) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_59 :
    recurrence5Scalar0Main.coeff 59 =
      -((((13312682411237510296247034369901087745547210180550069 * 10 ^ 70 +
        3982320203920097969226323214218653739614761453285931720983305263499369) * 10 ^ 70 +
        4393506216575059095597172077393979665336211859593436928782071215818275) * 10 ^ 70 +
        3606465466281665666621206318079244496580656684560158760344658221490747) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_60 :
    recurrence5Scalar0Main.coeff 60 =
      ((((466152065282829406012661958650727861452914056464630897 * 10 ^ 70 +
        6241485424835316972018171218824381411662185160755790360441907311678680) * 10 ^ 70 +
        8956727752781448273794059817699437748766769265866117932677348785440476) * 10 ^ 70 +
        6976198420599427145152449724264322893375191159909153719094968883736095) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_61 :
    recurrence5Scalar0Main.coeff 61 =
      -((((15494276264746044234672882584299722958378030781343907619 * 10 ^ 70 +
        0858743451154400114557956168929779872787378406057719802541460697858318) * 10 ^ 70 +
        2396863733599895332152281388334922413645110466771274711262890347374411) * 10 ^ 70 +
        9852078874740218662933805451724215781005850824104424078594195918768729) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_62 :
    recurrence5Scalar0Main.coeff 62 =
      ((((488980790293903345318192397364692499459273863525995536942 * 10 ^ 70 +
        1387758801722132403985832789637585353356645016507407789090438046337751) * 10 ^ 70 +
        3314159562320250913030643619876637975428049912748020953252521328382736) * 10 ^ 70 +
        5100014020377826405055414534683962935261204188046756935148801997942143) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_63 :
    recurrence5Scalar0Main.coeff 63 =
      -((((14652034141611896190106321717303693300176127265502632486623 * 10 ^ 70 +
        6979174327883406667639279506429947567879617447371536421149180581425385) * 10 ^ 70 +
        9869389509254933992563256124131150851167308684618144730021872700237345) * 10 ^ 70 +
        9796197845422054467502352183118749943714786314678376596170431355617498) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_64 :
    recurrence5Scalar0Main.coeff 64 =
      ((((416763478808678585205181179723451984758407954959680892572330 * 10 ^ 70 +
        9298065297228278034919973024182226985202860240259819245773669005628465) * 10 ^ 70 +
        1802583768348208093224891081962809916230304404620214379327776690602117) * 10 ^ 70 +
        6761828019208929099158217126844379541854422095284643102607771331424307) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 65 = 0 +
    65 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_65 :
    recurrence5Scalar0Main.coeff 65 =
      -((((11246671250441374930690535214004034851027366940198936907475980 * 10 ^ 70 +
        1111155055325472622763275049166758421059412302953983659591455370629327) * 10 ^ 70 +
        1417576826304156804958075557881572828232047745249718622313391342772713) * 10 ^ 70 +
        0750781737203443607895084267841699011550998370539976208041399116055473) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 66 = 0 +
    66 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_66 :
    recurrence5Scalar0Main.coeff 66 =
      ((((287648305386704951980935209435764762161931069460877249408390641 * 10 ^ 70 +
        7156622956088224553607424049377777295990422209132601953248713414161503) * 10 ^ 70 +
        4624152627995642740004909345688250978078782375043624491212957219492226) * 10 ^ 70 +
        0891499842349351003372642655911467831210196144608324567937054355916850) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 67 = 0 +
    67 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_67 :
    recurrence5Scalar0Main.coeff 67 =
      -((((6961171846550706656684773986001480995595556531430301447207935737 * 10 ^ 70 +
        8801682980072212160485507072450442093703909347959002193109091780644439) * 10 ^ 70 +
        7460077048669129853182162691229410039933492052884549319516527005582861) * 10 ^ 70 +
        3258938784414054148806461146309773315881576521030009239718496227829040) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 68 = 0 +
    68 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_68 :
    recurrence5Scalar0Main.coeff 68 =
      ((((158978925593883520165582308199303257384777601508831537076482465556 * 10 ^ 70 +
        4940945196741688063837662728808107062373220430369156674687426964184129) * 10 ^ 70 +
        8935033487714876712074767217337191969351442470297547768779664261655235) * 10 ^ 70 +
        8794359793699842930119755207486354628927744771372401667442231185392300) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 69 = 0 +
    69 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_69 :
    recurrence5Scalar0Main.coeff 69 =
      -((((3411977030693900248922384918766215387689876432905763975389659757093 * 10 ^ 70 +
        8734956507427877004012156675269048450090392236637198593633549790928809) * 10 ^ 70 +
        0185553443972352708389776006730327716058767351588939380945406530297542) * 10 ^ 70 +
        9643786737655191817571400856466267810585010891590774031262526676032846) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 70 = 0 +
    70 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_70 :
    recurrence5Scalar0Main.coeff 70 =
      ((((68340957529244204857325876415350412879815127952537361030476668582849 * 10 ^ 70 +
        2896072249421796071912430353765805034270884184591029267627363924285988) * 10 ^ 70 +
        3257495146349086476391472314669066605598787740157496031744192654866598) * 10 ^ 70 +
        6919097927497876540725969685678099455050322715575074819339620852192195) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 71 = 0 +
    71 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_71 :
    recurrence5Scalar0Main.coeff 71 =
      -((((1262235620095760302238681784319658605508362504647284483570351285163326 * 10 ^ 70 +
        4899832864634803187911185912407701804805625615317339167724994077723931) * 10 ^ 70 +
        3540857286269119881244665129207167175717122807156430093998784669523339) * 10 ^ 70 +
        5489772360320986157095931355504448408139246016413703445443786899671295) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 72 = 0 +
    72 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_72 :
    recurrence5Scalar0Main.coeff 72 =
      (((((2 * 10 ^ 70 +
        1006217074525542059758272420002609850561972470778267157852467843560178) * 10 ^ 70 +
        5113259289509867552450791190419812639303535330181176868369793363924576) * 10 ^ 70 +
        6675422090729664211007353491838069998479615223344590448454030957672929) * 10 ^ 70 +
        3896740301920488229413374252361478498728939892262399687021930699465545) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 73 = 0 +
    73 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_73 :
    recurrence5Scalar0Main.coeff 73 =
      -(((((29 * 10 ^ 70 +
        8841804306003958025280344535489425177119485357019878269161664204621317) * 10 ^ 70 +
        5112910294805610380807752728604451992032112739580438262554871708805883) * 10 ^ 70 +
        8733112919249083104992535080656006419657360773216582235906245579153373) * 10 ^ 70 +
        3797277466054598786772830932299031689489221005364764210508832381705051) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 74 = 0 +
    74 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_74 :
    recurrence5Scalar0Main.coeff 74 =
      (((((306 * 10 ^ 70 +
        8502097509232962560015640261641575861417724141344573060061312441162484) * 10 ^ 70 +
        3143445805380802181734774712557685683786854503510099930032816854430543) * 10 ^ 70 +
        2612498088487394239654874267858354128148418549706571678761978549017796) * 10 ^ 70 +
        8238511403277150256198929001126571806493879160312535675408070045305758) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 75 = 0 +
    75 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_75 :
    recurrence5Scalar0Main.coeff 75 =
      -(((((2 * 10 ^ 70 +
        6115398628591444153675692337433198752248722403496159598226307741278728) * 10 ^ 70 +
        5651759548430588978048913289308651202317868142964593770948348516140682) * 10 ^ 70 +
        9681472270936803438638994807583851490602654565115352934784147235315768) * 10 ^ 70 +
        5201990671095542280002787447246529816018518876082983796392870023975943) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 76 = 0 +
    76 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_76 :
    recurrence5Scalar0Main.coeff 76 =
      -(((((115383 * 10 ^ 70 +
        5672353865333035557267558565361586804368082353982500732751868983177186) * 10 ^ 70 +
        2583214795796217829179777473677289535835480349533018382528793036873378) * 10 ^ 70 +
        5599188740142928585808589607945464907851744941665589251945891638278436) * 10 ^ 70 +
        7584755376835034075867525302308014806980157253272687463042240901144595) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 77 = 0 +
    77 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_77 :
    recurrence5Scalar0Main.coeff 77 =
      (((((4235390 * 10 ^ 70 +
        4756490423567126023050535657045999060598807993295323118531795536978663) * 10 ^ 70 +
        0166932314565755464691198373673972836541915275948197757304278030846306) * 10 ^ 70 +
        1063682440404320540812703806575001992366401542995056902232390633097029) * 10 ^ 70 +
        5008077226261155907089871612582667994013504433618277731261066434808381) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 78 = 0 +
    78 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_78 :
    recurrence5Scalar0Main.coeff 78 =
      -(((((112414434 * 10 ^ 70 +
        3474052621101805413453376587958178883105533591046071602580130395823787) * 10 ^ 70 +
        7156855494720541290443585586702849791519445847201505446239722513497115) * 10 ^ 70 +
        0259004288845622827173213065341093647542173446320385445737453270832091) * 10 ^ 70 +
        0532382230992484234965114896525729692459453389773190361646220129366587) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 79 = 0 +
    79 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_79 :
    recurrence5Scalar0Main.coeff 79 =
      (((((2558442503 * 10 ^ 70 +
        1623671828674947368636698525532593090174305239308058608970525308308710) * 10 ^ 70 +
        7020778322322989108328524908827323306745732959067630427617321152791793) * 10 ^ 70 +
        3851894373760409298453114513015905811685689993586065185552901158642166) * 10 ^ 70 +
        3283338492240849610727778433657481601259796419986865624738925586910419) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 80 = 0 +
    80 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_80 :
    recurrence5Scalar0Main.coeff 80 =
      -(((((52685929526 * 10 ^ 70 +
        6809304742771922962009317327604704423173816970128340199690944156330231) * 10 ^ 70 +
        2124605162027257023039587070003415009550841664907293499560205304645013) * 10 ^ 70 +
        6076164251106196500388802280581538924460769257317080158677984261274962) * 10 ^ 70 +
        8384376839701311037488763794074605769251584907847061757176061618990639) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 81 = 0 +
    81 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_81 :
    recurrence5Scalar0Main.coeff 81 =
      (((((1005736262212 * 10 ^ 70 +
        3524124278497104358961495008392444760743861922009199460924217690178896) * 10 ^ 70 +
        3970214965554546897812555056433511283361525729526978364138910119332634) * 10 ^ 70 +
        6920192314132125229299264888722151041620641878316290178664316948792317) * 10 ^ 70 +
        8929429681338204423495593548635313662164200404393672331744440845708376) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 82 = 0 +
    82 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_82 :
    recurrence5Scalar0Main.coeff 82 =
      -(((((18031698050689 * 10 ^ 70 +
        6784844416753512927150919830269347034510606010996265847470517663628269) * 10 ^ 70 +
        5650134425428193253717540524199094887170607445158700158475334682696327) * 10 ^ 70 +
        3983707844580708304299803435929829103334899673196480247106689333223733) * 10 ^ 70 +
        8515908166369681468719327311321519549944933784174997801945919082538709) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 83 = 0 +
    83 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_83 :
    recurrence5Scalar0Main.coeff 83 =
      (((((306072668423466 * 10 ^ 70 +
        8338229412058488620145630035333353964915563342457123780048240561275981) * 10 ^ 70 +
        1158954322869116076876783502351459484678505217109092355348048963426873) * 10 ^ 70 +
        7903774695188506229721155673264961482130734673567568012524847103720531) * 10 ^ 70 +
        0724697698410028830433920238655328791920282923222541346113863748123954) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 84 = 0 +
    84 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_84 :
    recurrence5Scalar0Main.coeff 84 =
      -(((((4944826629142606 * 10 ^ 70 +
        0410418628734892037333384972459984428643481907772391140491373090739198) * 10 ^ 70 +
        4732733953771082742593801195166426291296442851756681255080406044465845) * 10 ^ 70 +
        8361808416314574538496219256411977010806767177367695839791766861289410) * 10 ^ 70 +
        8960531221585834081401082951189886324549382697691262131333100642100505) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 85 = 0 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_85 :
    recurrence5Scalar0Main.coeff 85 =
      (((((76320939788019984 * 10 ^ 70 +
        3075354295484563434151520588963543342694056707491079214214643979427039) * 10 ^ 70 +
        3137509716097248885417269408024101694459571023385661553003366326887145) * 10 ^ 70 +
        1824627569937740393144667211293577347478649091856507604992676444042992) * 10 ^ 70 +
        4418485636182547134681535505180132789840366831200015426392431969655320) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 86 = 0 +
    86 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_86 :
    recurrence5Scalar0Main.coeff 86 =
      -(((((1128525617854094693 * 10 ^ 70 +
        8053062843739658448151017232992655051518562492812025465152709273713745) * 10 ^ 70 +
        2663974471398640775956747672918148466338466708042027375453883158777772) * 10 ^ 70 +
        4839855784856269178799881249963928318688736991264214619972371010690261) * 10 ^ 70 +
        9265346241211366161058171295526960495279634122301658970394778800109778) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 87 = 0 +
    87 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_87 :
    recurrence5Scalar0Main.coeff 87 =
      (((((16020991713006026643 * 10 ^ 70 +
        5896535887130175079096871288390238291101467208065805525507949788321990) * 10 ^ 70 +
        4653933804855704046928348894432428307056734945545473074419538883626927) * 10 ^ 70 +
        4484752172350900536889413072299442063736157323171265445240916561291370) * 10 ^ 70 +
        6334426270704464358582455965655406931141842926807191422624750101599369) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 88 = 0 +
    88 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_88 :
    recurrence5Scalar0Main.coeff 88 =
      -(((((218738762809855202598 * 10 ^ 70 +
        0351084438374506215513571170728458700275226667341210854689821726336796) * 10 ^ 70 +
        2722740284678209079737916912460045630278697995321464180714950312987414) * 10 ^ 70 +
        6790034735062488773977938328549645558333227722216913900202859378139992) * 10 ^ 70 +
        8980329687558750188896145598528901781010390864255743760442151676255195) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 89 = 0 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_89 :
    recurrence5Scalar0Main.coeff 89 =
      (((((2876312451889623937536 * 10 ^ 70 +
        4735128351404090415865298201178190734736053920808622068391064745096963) * 10 ^ 70 +
        7010728882196357669836067349837702403968622694652257705217689927322180) * 10 ^ 70 +
        2082635900538175076681579656789956663343600865770500637877869444212406) * 10 ^ 70 +
        0521280391212803031208199533338088385285108266384135041098528364805878) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 90 = 0 +
    90 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_90 :
    recurrence5Scalar0Main.coeff 90 =
      -(((((36470276080154038695842 * 10 ^ 70 +
        8833907766241181721297931599805965874643986040052273281100160384568900) * 10 ^ 70 +
        2651112025208528698941070661130484149505623075919423375906109711470374) * 10 ^ 70 +
        2888517122865925443712487788858642291030349801062962052470312435633335) * 10 ^ 70 +
        9414983538227125046930644901574192682040431416743263210357841393946078) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 91 = 0 +
    91 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_91 :
    recurrence5Scalar0Main.coeff 91 =
      (((((446355393110021999540032 * 10 ^ 70 +
        5079448159948924030420228018057279926478160427449443056498078533183858) * 10 ^ 70 +
        0361220628338902989051609807820866233045831762227191382380356226462364) * 10 ^ 70 +
        6799447331258512487870739936291419792415120555860953572503247966239966) * 10 ^ 70 +
        4382049861283196181007412888412231502542863777912140387777068444613905) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 92 = 0 +
    92 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_92 :
    recurrence5Scalar0Main.coeff 92 =
      -(((((5277783206787974104637425 * 10 ^ 70 +
        5298027888334081548680111992211636406090794711173005287047571198459455) * 10 ^ 70 +
        7132088559289321927998317875923545805645978144605770827250609479137957) * 10 ^ 70 +
        5467637343927998388173757438301948793092725893642356301522881709588857) * 10 ^ 70 +
        0994748551065099013656878315172658962525395415760484466278420998121566) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 93 = 0 +
    93 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_93 :
    recurrence5Scalar0Main.coeff 93 =
      (((((60338969624270724435232576 * 10 ^ 70 +
        8338556515091674460116610885203181390716354888655219815864706848187616) * 10 ^ 70 +
        2822098167940020586674722937545096200557239982621963138745220654384850) * 10 ^ 70 +
        3649018175816289840176568891521510946672242373395780218110877125706334) * 10 ^ 70 +
        1146193163886834398185313488032403929906028189546981952504516777711905) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 94 = 0 +
    94 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_94 :
    recurrence5Scalar0Main.coeff 94 =
      -(((((667469573121263771020037055 * 10 ^ 70 +
        0328990092504274210775797406626280599175493631610519376888628526422339) * 10 ^ 70 +
        8346182033671604317787065696606804207249982455628647741191941776081309) * 10 ^ 70 +
        4495446638335918663181390273536430645126361731215138555040981888358370) * 10 ^ 70 +
        1345851238929281748381487473472556853701605893148688421083146805330096) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 95 = 0 +
    95 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_95 :
    recurrence5Scalar0Main.coeff 95 =
      (((((7148840896160521879351454124 * 10 ^ 70 +
        9329440989822661275990411988177997181668272201968359540678738533245153) * 10 ^ 70 +
        6235361447226270756725962805586957491571089915640677866371453459475092) * 10 ^ 70 +
        5383673874952545387179836813736767255495181136186646566300322252210240) * 10 ^ 70 +
        1122305773483706054956269876436697401183133062752285509988981755139750) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 96 = 0 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_96 :
    recurrence5Scalar0Main.coeff 96 =
      -(((((74177187739313007071664078653 * 10 ^ 70 +
        7538859385032237696939757743083244548580860324926508582545725793894088) * 10 ^ 70 +
        5196059891446214503554340121820774169743961010764217093745051443280918) * 10 ^ 70 +
        2292328504930006084910488436389993793712351418619987138272559903484793) * 10 ^ 70 +
        6214812595677736639737302886238168511680505346418309959982168092276552) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 97 = 0 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_97 :
    recurrence5Scalar0Main.coeff 97 =
      (((((746064154675520592582494270916 * 10 ^ 70 +
        0995295039809173063272006254466696981774136205944792300499180499225071) * 10 ^ 70 +
        3662955818400407191206963874898274781464767728003975059644098402019898) * 10 ^ 70 +
        2165514451054293393092477064612805432876566303863081112834021590660492) * 10 ^ 70 +
        5085268580009788232207019995720325325443413676449100324503002988846774) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 98 = 0 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_98 :
    recurrence5Scalar0Main.coeff 98 =
      -(((((7277413855136261217919724530762 * 10 ^ 70 +
        2483531968451606981899381565295103333818076265710627227265542865102174) * 10 ^ 70 +
        1823284601747312952531017257997272620843135201762245127230615887024291) * 10 ^ 70 +
        3878400695202658522205200955350725832847877882586805858283795080470972) * 10 ^ 70 +
        5979386061153526403074212857683308202779285172878305159114708184608469) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 99 = 0 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_99 :
    recurrence5Scalar0Main.coeff 99 =
      (((((68878384387257660863110096722544 * 10 ^ 70 +
        8822933971891807783736738649486444293570120131577558666792891443777255) * 10 ^ 70 +
        8996614035877379681658646747441789222871059324501832626696933274311474) * 10 ^ 70 +
        1022271701960801435109857307470175205124151318092258720114540403589554) * 10 ^ 70 +
        1292994274678190413297831765592166537861908455085132110484747421020234) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 100 = 0 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_100 :
    recurrence5Scalar0Main.coeff 100 =
      -(((((632836445290416743734393985565515 * 10 ^ 70 +
        6061281730022003301147567027694264478423697213994013753803107556537041) * 10 ^ 70 +
        4127098737644228198071582209938055551712351455833720680403293517888851) * 10 ^ 70 +
        8870688738716502952469365175847630811403058085062477247278598352465769) * 10 ^ 70 +
        9270464962098754769456331770602835938274771952785207276978056326153224) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 101 = 0 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_101 :
    recurrence5Scalar0Main.coeff 101 =
      (((((5646634237169576759861496851624502 * 10 ^ 70 +
        9989888855411169120772842480889106893006236512820875565212941833414340) * 10 ^ 70 +
        7051756698546153279719872306578008543924328781824456892346123535923979) * 10 ^ 70 +
        6229822775322496955213666382505181335839371891729489684435227373817707) * 10 ^ 70 +
        4883399167821124164528274879147928182219332887003627862101768522898173) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 102 = 0 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_102 :
    recurrence5Scalar0Main.coeff 102 =
      -(((((48950264604287662694463491235590426 * 10 ^ 70 +
        5820746628383939867808595477480534320322519192151018484049739609999700) * 10 ^ 70 +
        7354329705600312125264966019414257344948796245263658145593611152590909) * 10 ^ 70 +
        3623752995619315840930294811829328745526554715925139828844560019622855) * 10 ^ 70 +
        5003447787081883794823356679696390556460864787317140453556786384138720) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 103 = 0 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_103 :
    recurrence5Scalar0Main.coeff 103 =
      (((((412436244196466661789956496343891601 * 10 ^ 70 +
        8704775938304747803916796547308645602575593654403548104576668896394227) * 10 ^ 70 +
        5430347555360513498567754707627630318643936433175238491556569565269412) * 10 ^ 70 +
        5447935311069819629667471604237124618689236586606436693488668181379735) * 10 ^ 70 +
        2263773937019506041226013185515731508791846414213263397686052104204127) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 104 = 0 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_104 :
    recurrence5Scalar0Main.coeff 104 =
      -(((((3378754616392856600829959844513055481 * 10 ^ 70 +
        4856233641584041903617372306058632157014374192246721077511028762064593) * 10 ^ 70 +
        0023599049814736744461830077876801255718898689172821935844848124481582) * 10 ^ 70 +
        4336378303239312682176356683866939044321661141936979504777964000699992) * 10 ^ 70 +
        6111615744298074193202601360147087960041638390327432085219489214182738) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 105 = 0 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_105 :
    recurrence5Scalar0Main.coeff 105 =
      (((((26922128013505019498238773580641581874 * 10 ^ 70 +
        6021597856673918496537404284362539288959291144554669468865418983740777) * 10 ^ 70 +
        3514982157958155389112754198765386144302024963948272974294338636750968) * 10 ^ 70 +
        1732593387685552571679123016124598337328071751474356847944573013248647) * 10 ^ 70 +
        1274373929422693078189442723332465123894098613861023106573711649971301) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 106 = 0 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_106 :
    recurrence5Scalar0Main.coeff 106 =
      -(((((208719817884942624163512902741155821001 * 10 ^ 70 +
        9478353352667878895584644462134901363796307304711519914268480278670561) * 10 ^ 70 +
        5819113248926734902406685310149397072963340522746824143228769532524282) * 10 ^ 70 +
        4720346837451005005855849854024706173373692688717481069297167340011634) * 10 ^ 70 +
        4632465106143578661000575536489080815838753359308095918043882246338142) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 107 = 0 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_107 :
    recurrence5Scalar0Main.coeff 107 =
      (((((1574934709146204471052928245751592767184 * 10 ^ 70 +
        9199209501502300759393962980851427398139457479769609205691472738562469) * 10 ^ 70 +
        9872412510748522217688957556822936098826405977156939846310958270219788) * 10 ^ 70 +
        4936857428446736574076777502154622216750535320532445503538088703157467) * 10 ^ 70 +
        3245454745837334106240101800358857946573453729953378016042090440791739) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 108 = 0 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_108 :
    recurrence5Scalar0Main.coeff 108 =
      -(((((11570277056984942133925319498880732999795 * 10 ^ 70 +
        9300246027429388470071722125555442373294873391548734472933292983735401) * 10 ^ 70 +
        6945797465461118553644639965357746170085109953993403086481095249040486) * 10 ^ 70 +
        1591663829983668828352512866466820145665288533134249355474558928905500) * 10 ^ 70 +
        1446017718319069548832499290427603416893824377318261137366389519668480) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 109 = 0 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_109 :
    recurrence5Scalar0Main.coeff 109 =
      (((((82782823157911520496626784215185963640477 * 10 ^ 70 +
        2862007872434811834903702294520920153482819876627361968897243413248208) * 10 ^ 70 +
        5124499845929538838939968402909068588354631744942618148819736545411164) * 10 ^ 70 +
        5728485759927357779983980781161721027575214665479759082415038524402338) * 10 ^ 70 +
        6998353843456984622236283527951375801507162671384468791830234904600705) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 110 = 0 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_110 :
    recurrence5Scalar0Main.coeff 110 =
      -(((((577006102806154739875978817516862665561224 * 10 ^ 70 +
        0206863248973348958818467794427895752217547311707476921175572303825084) * 10 ^ 70 +
        7271989810165212330021651292215682911239235903091493377771905799414208) * 10 ^ 70 +
        7570242608102552976432450728351829972232714776437841005777661957303165) * 10 ^ 70 +
        4538394074174421325920032504371325604715058172415895360012489332897417) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 111 = 0 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_111 :
    recurrence5Scalar0Main.coeff 111 =
      (((((3919119389664327186862298490825198911161413 * 10 ^ 70 +
        7303007067461210490119575218465921388290653229307763939581881680251467) * 10 ^ 70 +
        4313989243442855671481608407744883446506215051237593370126167933249298) * 10 ^ 70 +
        7380970501594060759177913894102764845101465273752312120343697130774253) * 10 ^ 70 +
        0618950657012396612303800041296774905182207031754070216929787530082495) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 112 = 0 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_112 :
    recurrence5Scalar0Main.coeff 112 =
      -(((((25946856636523094045005865670074621654811559 * 10 ^ 70 +
        8745199760345975316324360822513605900147984836667298423936066073525097) * 10 ^ 70 +
        5735518850000625863856342713262172243822196176934324284661144937856545) * 10 ^ 70 +
        7812979591091221482195442225911147885518710702947495110406026685403730) * 10 ^ 70 +
        7218134047576461020897950623743120751766655379014635374609735793030734) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 113 = 0 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_113 :
    recurrence5Scalar0Main.coeff 113 =
      (((((167488775742758269072277760738709730549601434 * 10 ^ 70 +
        0956069707333111455217914954553353657019178440227704015804200620533257) * 10 ^ 70 +
        9743786497703317491736995683858234876557220338320866899712171996699485) * 10 ^ 70 +
        6305074558062194591129669649176650819308687321471060902864708264530452) * 10 ^ 70 +
        2166990265330015648134229284269439401792666097293378292882265317915756) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 114 = 0 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_114 :
    recurrence5Scalar0Main.coeff 114 =
      -(((((1054397473760676455095295067592568232190112619 * 10 ^ 70 +
        7644794033931129991715666218410686337232162939239411728601522790527970) * 10 ^ 70 +
        7289342642813749583637649400503221036780844037587822110744819289673920) * 10 ^ 70 +
        4414625201971046445978591960432559416038181577780245393872993317434721) * 10 ^ 70 +
        4417103177771382157109786802556103227625882094990347529795988758309896) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 115 = 0 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_115 :
    recurrence5Scalar0Main.coeff 115 =
      (((((6475157576698075102960609981926426871720533065 * 10 ^ 70 +
        1897642479331189997855413979982352532338667697255558812552334508855285) * 10 ^ 70 +
        7832608539809476241660254921979552800958097759537559730083106112637948) * 10 ^ 70 +
        8642122327860960932042203673263216722918805352013168949731962613679430) * 10 ^ 70 +
        3071793374645084000531700005563790624882324342885346225377549367463744) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 116 = 0 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_116 :
    recurrence5Scalar0Main.coeff 116 =
      -(((((38799856154159468320425708007645248606737754974 * 10 ^ 70 +
        2384360513023145227483251262352114249218127908907775060964272203983684) * 10 ^ 70 +
        6250404379304610972298828210128859082583126714294745242716222499681124) * 10 ^ 70 +
        7843581445082681088670524943845052123345984611333531263791122532556987) * 10 ^ 70 +
        1188874680471711291248749767002913801118000654537631275302197129057521) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 117 = 0 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_117 :
    recurrence5Scalar0Main.coeff 117 =
      (((((226906576982902765379067320979609734632075411419 * 10 ^ 70 +
        9507502158797852771899924628020886662949491486008403165383191474267663) * 10 ^ 70 +
        7779082986934078720957806118540913524043317162348583934593608643923054) * 10 ^ 70 +
        9051462584892782241241787769981982335079000752138081987499241152419883) * 10 ^ 70 +
        2654198205530337437860460913303329170248443840932436315491860610354245) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 118 = 0 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_118 :
    recurrence5Scalar0Main.coeff 118 =
      -(((((1295393575595166799327761857928296621079471368923 * 10 ^ 70 +
        3255273501485173647841159527696178908769872111200793172014849565707310) * 10 ^ 70 +
        6948918373712377027465309808882314226048589666269972466030445039106555) * 10 ^ 70 +
        3307807820712282775035579872258789425374948913388434643377153847454353) * 10 ^ 70 +
        4719638107345024809038693416838942627267900517698101606984448041447669) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 119 = 0 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_119 :
    recurrence5Scalar0Main.coeff 119 =
      (((((7220907375928945822856214764937299297323939136796 * 10 ^ 70 +
        7809823392894499250803303117084358738217685165346603114876432420810779) * 10 ^ 70 +
        6546309771529328269787096570153166184649934378209899383284464401895018) * 10 ^ 70 +
        2527153533572895982754147961096894621244134123804411165684531990391564) * 10 ^ 70 +
        0101627974133503368011324619504495757188645475438871589634724393494359) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 120 = 0 +
    120 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_120 :
    recurrence5Scalar0Main.coeff 120 =
      -(((((39310828647536969835831949864220126238826183790951 * 10 ^ 70 +
        5413706677923402433709504004407913433003292473501788439475926200549920) * 10 ^ 70 +
        7755963512183470915402235722990588913497313065469243712288924648756343) * 10 ^ 70 +
        6963445944506337478086293522738224866761939248205645398946383789678456) * 10 ^ 70 +
        5537439364142674197120727395863525797492925031165617761088719430709041) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 121 = 0 +
    121 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_121 :
    recurrence5Scalar0Main.coeff 121 =
      (((((209052532729867495274499354472482557346859058672849 * 10 ^ 70 +
        2250679024020225393323156783129324486760221799050343838149973679501943) * 10 ^ 70 +
        3019525087095294230434927722426677970221615086247708299172576403222177) * 10 ^ 70 +
        0438969862417584392118273364122798149588045838710931453125663879485986) * 10 ^ 70 +
        9788746794131528473703893747176130436500933655046728616489692182089572) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 122 = 0 +
    122 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_122 :
    recurrence5Scalar0Main.coeff 122 =
      -(((((1086204022514687780760156335479120333559092590021271 * 10 ^ 70 +
        6050275900505087849431024153481200193015268492011897762569988698372789) * 10 ^ 70 +
        5125448376161742049261982592368081968999784752473453953716619754371544) * 10 ^ 70 +
        4347710662884676439285809541781048151818375056459549625309593269150893) * 10 ^ 70 +
        5242485613086681732946278317486438854480235941813398585367470898965287) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 123 = 0 +
    123 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_123 :
    recurrence5Scalar0Main.coeff 123 =
      (((((5515280916939257203815244128911099750222861526924812 * 10 ^ 70 +
        2496392679069773341834509278873200375982383735458920572121404005806404) * 10 ^ 70 +
        9097670052720012402123501928351906967085698343795692961708509466587163) * 10 ^ 70 +
        2323963738900252273820487020465059275378571812051237350136469854195259) * 10 ^ 70 +
        4944098227250093079216686420857571209308418696266634064988226454960592) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 124 = 0 +
    124 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_124 :
    recurrence5Scalar0Main.coeff 124 =
      -(((((27372175622666761021703838624944644523436687629818307 * 10 ^ 70 +
        0222785823597937588783138805401977575161590320128477534168666014136496) * 10 ^ 70 +
        8669889714050198115457003830726506696085759036286635871679509264919189) * 10 ^ 70 +
        5360322293865939881766311784873042101239158815707101218111057252497105) * 10 ^ 70 +
        1574720466021213115240267842207997198073864268763168487538964661589245) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 125 = 0 +
    125 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_125 :
    recurrence5Scalar0Main.coeff 125 =
      (((((132806516149240328168350543512385304226565892845437681 * 10 ^ 70 +
        3495781961600254775141728282760277113513871135559531972331908993762704) * 10 ^ 70 +
        0869886157040962747504889304489571416579405116032645908684459016786554) * 10 ^ 70 +
        2802636768606162260067849944467519711337377242838614739463406609083521) * 10 ^ 70 +
        8089581910543685021963398269825697398307997355645413270635157219295230) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 126 = 0 +
    126 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_126 :
    recurrence5Scalar0Main.coeff 126 =
      -(((((630055186415657057431815603263629107143125011699610228 * 10 ^ 70 +
        7070490315998503358806713851380655728491375571268677700212485198809254) * 10 ^ 70 +
        1633306409664836209058545004825460839888857233480624855760844996469565) * 10 ^ 70 +
        3441601844067422782831960091984729629018188843120244467853792442667984) * 10 ^ 70 +
        0512811585983212503557997113622797155791351308834074083100514411899585) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 127 = 0 +
    127 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_127 :
    recurrence5Scalar0Main.coeff 127 =
      (((((2923247414496159180007816068524023263268840626113006999 * 10 ^ 70 +
        4949404273676756900701828897058313015744171976757435622014505403176466) * 10 ^ 70 +
        8203285533816013100531242212565986539226813237627210958229134441964371) * 10 ^ 70 +
        0597507149030045560131963981167515773926431153618563724510843665208880) * 10 ^ 70 +
        3256040752778977808473408684820604636413572454340312694747973678408783) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 128 = 0 +
    128 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_128 :
    recurrence5Scalar0Main.coeff 128 =
      -(((((13266516929997293438003953541953362235799044192495849828 * 10 ^ 70 +
        6266316015371668286755479435849118825605975295580904946030175545251172) * 10 ^ 70 +
        2926883737303009400857090822255239065749745311069381241380014122533043) * 10 ^ 70 +
        4020488259749434445954987583592114414399775883936568453625496645284185) * 10 ^ 70 +
        6372233168208387131794005479108627545121055399872566697606882401179687) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 129 = 0 +
    129 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_129 :
    recurrence5Scalar0Main.coeff 129 =
      (((((58901614713113056431747384016145579552431375266781396205 * 10 ^ 70 +
        8300640143063630892221190860849963638665358868421066282913116741707832) * 10 ^ 70 +
        4354751844372218062633213426080129973453526683588534199109578922350596) * 10 ^ 70 +
        9017143797843383848083349169928191700417691131648225542652415511976170) * 10 ^ 70 +
        7121768859034208647595316043944603247152882566176706954767526031456179) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 130 = 0 +
    130 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_130 :
    recurrence5Scalar0Main.coeff 130 =
      -(((((255887502611396750242402605173550097583127833740624827830 * 10 ^ 70 +
        4123713653953808117405418625426888538668145015871650577257820242548748) * 10 ^ 70 +
        7194606650609097970212166176439144350469589243858816246025788227528818) * 10 ^ 70 +
        6861986010579088778838009575477032606466905742848329769735937519303357) * 10 ^ 70 +
        3103765440383919576985063372052206076861085932550108174007680888316894) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 131 = 0 +
    131 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_131 :
    recurrence5Scalar0Main.coeff 131 =
      (((((1087910835617722575952501930879692736168800824163923332824 * 10 ^ 70 +
        9828332550074982518658984364113833050273424544731033691556323705991544) * 10 ^ 70 +
        3875408868062066293091550908891040286871216811832731132744140059043762) * 10 ^ 70 +
        2310279894532047849013598641874580489841853321764158314657762590317092) * 10 ^ 70 +
        1176475709091786936159668956489582893245499587691662686000500993017118) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 132 = 0 +
    132 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_132 :
    recurrence5Scalar0Main.coeff 132 =
      -(((((4527190904961871512722047454248875617174006826930928891140 * 10 ^ 70 +
        6651652753255755605693900363808503262267034173434950327646162284549532) * 10 ^ 70 +
        9535166175218691733673484884368224470925088764869855774976173109942560) * 10 ^ 70 +
        4811174131104783914792244969794161377881812923910990687268404897981888) * 10 ^ 70 +
        2904004292699823527727737671801107432995078163225317937295151420611605) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 133 = 0 +
    133 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_133 :
    recurrence5Scalar0Main.coeff 133 =
      (((((18442625110990929372621561375457534140373155334302497443189 * 10 ^ 70 +
        4619974917773372173292173816648558516420313642798536882432492508251044) * 10 ^ 70 +
        7029449550350776457137405568139262035599472425042543748863478126010832) * 10 ^ 70 +
        4957453067475724582577594689383108327751884330891633055031503708227616) * 10 ^ 70 +
        4412316789645280986204139377097437720051792929748267749760894416693823) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 134 = 0 +
    134 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_134 :
    recurrence5Scalar0Main.coeff 134 =
      -(((((73559793366677350971073763244473017773831771344560503793445 * 10 ^ 70 +
        1778314647449559316869251890672650087260758150076028706702837220263006) * 10 ^ 70 +
        3926217674780898098718324423739665395187184340692864701880168585913032) * 10 ^ 70 +
        6638813134806887397599868533312884120307291260582622502274177142599491) * 10 ^ 70 +
        5610011866254485871174259077478702626814875446023021129316583600969926) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 135 = 0 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_135 :
    recurrence5Scalar0Main.coeff 135 =
      (((((287306740183365314733243580843364424881922551666211194051836 * 10 ^ 70 +
        1896971996101991440262075601249427088952847092378368565745374795528788) * 10 ^ 70 +
        5513932566642554098989618163435355331387713110988322701262124495933791) * 10 ^ 70 +
        0988987445273901585949514809287465531282485570291365003906162850188820) * 10 ^ 70 +
        1213500098923802776121373986103501124161448492717076040784419218314270) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 136 = 0 +
    136 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_136 :
    recurrence5Scalar0Main.coeff 136 =
      -(((((1099007749838937205413072386618814224264649488972424414347652 * 10 ^ 70 +
        7531264941299863209276256853726409263014632784752423291608094337035054) * 10 ^ 70 +
        8497090823680602268025581645778725224052710627539507975713995933144889) * 10 ^ 70 +
        4075729678660111647055146346039186228280128844015075479278227833924191) * 10 ^ 70 +
        4308663592412749601295283908351666709803557337862910650928796854172893) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 137 = 0 +
    137 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_137 :
    recurrence5Scalar0Main.coeff 137 =
      (((((4117805174417360860796731436421639037003383772466391245655731 * 10 ^ 70 +
        5138132026414461206322973119359750969230079909442208445452018320464474) * 10 ^ 70 +
        4817638315193232657229132719700046940308281216266491555180383194341491) * 10 ^ 70 +
        0450097275859703935278115812522438618624080718180013710732270537806749) * 10 ^ 70 +
        8210344999119523108594535433538701027646529909136384520232727069246181) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 138 = 0 +
    138 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_138 :
    recurrence5Scalar0Main.coeff 138 =
      -(((((15114711051583239822513275829508182662098187105745562534627205 * 10 ^ 70 +
        8825394798299072004502572748631337482699511142095075230900585194599283) * 10 ^ 70 +
        2235628261993034853506032194815086548785203967465843010457364013011815) * 10 ^ 70 +
        0257975498071525476744016447273100600461769140037488506542464764445489) * 10 ^ 70 +
        8975420263620630822128831258498582587621950904533198751782831775923156) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 139 = 0 +
    139 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_139 :
    recurrence5Scalar0Main.coeff 139 =
      (((((54357605027428490459938508628230384861711408366832409810772978 * 10 ^ 70 +
        3693440229490306943297707079842537923014173600530359444731633401643936) * 10 ^ 70 +
        2288690344134554931064567370408706487086865282196365705018088023667741) * 10 ^ 70 +
        1029655510087947961350112888904765858848075717048144893069086705182173) * 10 ^ 70 +
        7398853536820647888070511455630252200662561510083885088522846496290267) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 140 = 0 +
    140 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_140 :
    recurrence5Scalar0Main.coeff 140 =
      -(((((191559240480450257867108901708750095566394568615185602121222522 * 10 ^ 70 +
        5176918101378787325371238088880315751254029089579551441761336306252484) * 10 ^ 70 +
        5850464031626858099758207351159539262809337548745449815628811209222594) * 10 ^ 70 +
        0289587192031510450587151167214373106738245376065329298251265714256513) * 10 ^ 70 +
        3633358878792358431974260056617827439404611231089220922051042314671189) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 141 = 0 +
    141 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_141 :
    recurrence5Scalar0Main.coeff 141 =
      (((((661580515326277010934383620892352584618353466327211923151926814 * 10 ^ 70 +
        1109177824515182238236440890177026510381708262994904867290631481902378) * 10 ^ 70 +
        2913229552809212678130687046805617129651744629954592810468533063274523) * 10 ^ 70 +
        8538976530792715677824202188473496395548195905336465260728075549772052) * 10 ^ 70 +
        6301577513228477678266416902662432466427953307694522374772690761333170) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 142 = 0 +
    142 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_142 :
    recurrence5Scalar0Main.coeff 142 =
      -(((((2239505788928864394606791249792020775942374715068904401786402751 * 10 ^ 70 +
        4119993282110683869586857981033846231141678413168297926320118747566439) * 10 ^ 70 +
        9302264398936777791725458575920281227426597385258711139907251192816123) * 10 ^ 70 +
        0008796754488180610325171291976669473718051577645235031539626071705628) * 10 ^ 70 +
        0004991404472906639190449618832046250259805839412316419213234989249258) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 143 = 0 +
    143 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_143 :
    recurrence5Scalar0Main.coeff 143 =
      (((((7431273902346027603093780666186205590510711909718710052798381453 * 10 ^ 70 +
        3795253583546155146140366017072350036051512873800853897401979535673177) * 10 ^ 70 +
        2201566156605374097155380932969326265395173309415253285666026637780114) * 10 ^ 70 +
        5181142786044923637296110857532497479631020323644275034211023826785747) * 10 ^ 70 +
        6864893460151066303153083244103198064086034196202496384053001622868921) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 144 = 0 +
    144 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_144 :
    recurrence5Scalar0Main.coeff 144 =
      -(((((24174991389582003881947692590117085428638666834937271836739112831 * 10 ^ 70 +
        5813408498444152137485473063960868487641782253033391388202987885927890) * 10 ^ 70 +
        6289721209818045487248555651782927133532697078490531193124816296683182) * 10 ^ 70 +
        2338099223519953769103372168227817099396432797292503336183512294622894) * 10 ^ 70 +
        8041478467800026728682091090835700238479441138098567399546664800561592) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 145 = 0 +
    145 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_145 :
    recurrence5Scalar0Main.coeff 145 =
      (((((77109956352988907505599386838748093379711965198023847192554395209 * 10 ^ 70 +
        0724118064822383585204100309491362783329164413841622762080555911875471) * 10 ^ 70 +
        3924514253646672085348795291488205938601170928414084285992464849381369) * 10 ^ 70 +
        2145449537098395448299179650886997096807418229658645635970453053678507) * 10 ^ 70 +
        7214245531913241417491740364726152034907485245714195465312735344203284) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 146 = 0 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_146 :
    recurrence5Scalar0Main.coeff 146 =
      -(((((241181220012486037237976352193520900295746451759877931267121448178 * 10 ^ 70 +
        5751646327788388995434011152601045713757164201561888384700034553705949) * 10 ^ 70 +
        1589856682268071256160788529186586069354702147380371872061016606029553) * 10 ^ 70 +
        4940932293916558878753748204355327183085862029086274235949275617380562) * 10 ^ 70 +
        8549539489890749130767075074023573861605901347254210700780873591571112) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 0 +
    147 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_147 :
    recurrence5Scalar0Main.coeff 147 =
      (((((739796078608136446161342572934737739420628035268405563332082076475 * 10 ^ 70 +
        7299593233581535818482378790179993259993448765910693622822327998289841) * 10 ^ 70 +
        9834008931726311562111840077229859357549051200558006087278313909295774) * 10 ^ 70 +
        7985530656048697300165689559626296451952166417632409466675779074207637) * 10 ^ 70 +
        2956072180432421085317149494224784082876860507336925303432769638294722) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 0 +
    148 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_148 :
    recurrence5Scalar0Main.coeff 148 =
      -(((((2225673638734873877014299728077816800927750390152098846840782017601 * 10 ^ 70 +
        2751465730302649503141619137188727058169017927565377003791475149095398) * 10 ^ 70 +
        1301869574562576434100294435852168161864795179160795436951823215950087) * 10 ^ 70 +
        3637454184310925552364542544360994069020291046257765594779654615524312) * 10 ^ 70 +
        1866445133914362979412009659557116723968492580149372171173300078453544) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 0 +
    149 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_149 :
    recurrence5Scalar0Main.coeff 149 =
      (((((6568044870040364313557817307368380988526512290142389775106971108133 * 10 ^ 70 +
        4701018938298556012391881734128561431305940982733127659328083947854489) * 10 ^ 70 +
        1384858244501458395884609751859358087591589779075717215929033711418692) * 10 ^ 70 +
        3664257459016257830475194642591338284261323245730884032885661236154685) * 10 ^ 70 +
        6530534695101305376531700905417838782637954571474028029080770916883616) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 150 = 0 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_150 :
    recurrence5Scalar0Main.coeff 150 =
      -(((((19014242787962633863314069588124054369057384747295086133545634041943 * 10 ^ 70 +
        3893336129224424988561774632071343155053653348895769059802074558106248) * 10 ^ 70 +
        2447285485895389574893769984541494879761112822423633657420043766100860) * 10 ^ 70 +
        9908341414429369125351616785656750021250802797409198204696558802299235) * 10 ^ 70 +
        6598542690195025533878186747777539858451879833620788787956796798357400) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 0 +
    151 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_151 :
    recurrence5Scalar0Main.coeff 151 =
      (((((54004789540591919502434976984055347904161509369776334344177662463602 * 10 ^ 70 +
        0981363038869706311650546700693127467505855900705676616702854103809278) * 10 ^ 70 +
        0471365524818244512191823874842202858525149881165732328044844992429166) * 10 ^ 70 +
        7066396260768447283308673433888483425742885867914789417043753981512830) * 10 ^ 70 +
        7199382922606172073571549369832049184728348554230202077401466064031716) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 0 +
    152 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_152 :
    recurrence5Scalar0Main.coeff 152 =
      -(((((150500102257421773213756956776578060601285685682564304671360980262870 * 10 ^ 70 +
        1078849385990754622124712666130990609543593060219662165342891744793915) * 10 ^ 70 +
        7738178595860539726687390716958410264184444813656448044394367408297005) * 10 ^ 70 +
        6994424218605210228870583445292770672360157040145205642127756425269108) * 10 ^ 70 +
        4216502699382967038264049400147677859933964685105766375360188941807336) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 0 +
    153 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar0Main_coeff_153 :
    recurrence5Scalar0Main.coeff 153 =
      (((((411559377442530623646099543036096412714562953309351953930080096719419 * 10 ^ 70 +
        8205432224140677563867326073228269437488088915220655680450121530942263) * 10 ^ 70 +
        9978584867927993310832663226325182692447744338553710945030421317427969) * 10 ^ 70 +
        4458729041423025857953655489757271185249885154511504087418900706932156) * 10 ^ 70 +
        5041558203163187674917903187367332494966511885639181720261856169539702) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 0 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (154 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_154 :
    recurrence5Scalar0Main.coeff 154 =
      -(((((1104481133955000148338055899589564155981907848897079841582716364980186 * 10 ^ 70 +
        1374771512455189816793899190563670369623439045690360622600041385701194) * 10 ^ 70 +
        8181489014901295560214727460762189581933796784585502324203203279957553) * 10 ^ 70 +
        6514044193797210967814903631511872195382932372039615246967179225175255) * 10 ^ 70 +
        0724289700253890786434586525829533030257334096413601872378788030627082) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 0 +
    155 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (155 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_155 :
    recurrence5Scalar0Main.coeff 155 =
      (((((2909056236263223513729116323782230456981151139357241875029391812000398 * 10 ^ 70 +
        8369958729283191916560734148606894660505659422032669613419220264937508) * 10 ^ 70 +
        0528371172038261586281805669088949781841090154132414000052782735773233) * 10 ^ 70 +
        8630140702779821197564253960706742841322404876170679838081522873132987) * 10 ^ 70 +
        4654319048979767940207253752577930240177850652094652069005958883209711) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 0 +
    156 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 26 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (156 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_156 :
    recurrence5Scalar0Main.coeff 156 =
      -(((((7520572654274674671257253596031278924022392712489139732959833687102582 * 10 ^ 70 +
        3885319078434985870585302338426201698364724911774992916530825304166030) * 10 ^ 70 +
        7754727698490252356593096789836604050169137979650766813574684926651191) * 10 ^ 70 +
        5354674593100887521873148906791716312357922102581010682250650944415378) * 10 ^ 70 +
        3877252189429716588082543750455162879143108288270597897849309882599835) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 0 +
    157 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 26 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (157 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_157 :
    recurrence5Scalar0Main.coeff 157 =
      ((((((1 * 10 ^ 70 +
        9084936545731163807218094130696158204407017360634405735219728891925975) * 10 ^ 70 +
        3171357660809740735261240116124268790019519499514428874545064801362814) * 10 ^ 70 +
        8677981524912378291578855960821789747203128985379735113305146290958493) * 10 ^ 70 +
        9787186894136041609354826371324129548441844946380234165363683373611534) * 10 ^ 70 +
        0411726861138507674908441206562061667795135291477333603869949078020622) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 0 +
    158 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 26 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (158 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_158 :
    recurrence5Scalar0Main.coeff 158 =
      -((((((4 * 10 ^ 70 +
        7545199729977250356424490726246032804442755582728320213928317446624523) * 10 ^ 70 +
        3883628122003297085524667625468070190238568170789619516309666030089177) * 10 ^ 70 +
        2282369574230705965495504971047855452906474548013088617312764466468822) * 10 ^ 70 +
        4932345727935099734518443454709684405028390823192978907173419363233884) * 10 ^ 70 +
        4168663152200611627899520135247517535051062579026310167693439831464024) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 0 +
    159 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 26 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (159 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_159 :
    recurrence5Scalar0Main.coeff 159 =
      ((((((11 * 10 ^ 70 +
        6287499652161919905186382859097921915432335820176581976601126973962925) * 10 ^ 70 +
        6060254621181428983657371194260463346570439723517376032120480982209657) * 10 ^ 70 +
        9200634315842859086685773748858056905634314193163352798838105020316339) * 10 ^ 70 +
        5986688808600045552243562533725276595492052607414863463589080500529979) * 10 ^ 70 +
        3010714292518946128539430273366441291827238858806901736058840356610512) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 26 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (160 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_160 :
    recurrence5Scalar0Main.coeff 160 =
      -((((((27 * 10 ^ 70 +
        9256435911324353071291301928539825209647028183732403037184499549444031) * 10 ^ 70 +
        0591832502921189438980077767940063996028345095206299119147343319779936) * 10 ^ 70 +
        7140319581742389218388106203960750301225553901112726747975297586603052) * 10 ^ 70 +
        4866337115997685101610316720223284671811637051216615815559593683429564) * 10 ^ 70 +
        6541368208001107552056387915159881006511720122359000282321751135970133) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 0 +
    161 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 26 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (161 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_161 :
    recurrence5Scalar0Main.coeff 161 =
      ((((((65 * 10 ^ 70 +
        8490817656237927186792929420372644488671557867384626239491728025729146) * 10 ^ 70 +
        1544344870967188433886718739419059741255399807846271387652036819255350) * 10 ^ 70 +
        7364805817854284626897687912983810173319514550756961567817851554919079) * 10 ^ 70 +
        0162222816010982698603268501042205056770800081936513860249542978634623) * 10 ^ 70 +
        3840268066807237951444692024503731039611389151966355408414937040867589) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 0 +
    162 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 26 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (162 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_162 :
    recurrence5Scalar0Main.coeff 162 =
      -((((((152 * 10 ^ 70 +
        4770207181429895544168545197895091977361085663764814303334119222786275) * 10 ^ 70 +
        6036662617737822755724649656808122541328790745739183354516008881971961) * 10 ^ 70 +
        0399681331399877364772724288950180051128553723324022857590786934523319) * 10 ^ 70 +
        8071072196100357657085722657779906953313332294483827843222453837869470) * 10 ^ 70 +
        2417172606064228242539431495355763762239824900755615980663977039752769) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 0 +
    163 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 26 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (163 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_163 :
    recurrence5Scalar0Main.coeff 163 =
      ((((((346 * 10 ^ 70 +
        7354136199671636150147310209686920018624343933536137944352913563579370) * 10 ^ 70 +
        9876158818533488657287565250117671972402530134947736817537883821338094) * 10 ^ 70 +
        7725591265091121640647402042903476028620121151341795473135650446562448) * 10 ^ 70 +
        3670433889736585234553304494850764497909495210529347647449167592440350) * 10 ^ 70 +
        0545558947367008038085532369362491411805976399373287162444431443281767) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 26 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (164 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_164 :
    recurrence5Scalar0Main.coeff 164 =
      -((((((774 * 10 ^ 70 +
        3928952885221816564709675305796265191945545353094441977845138264878789) * 10 ^ 70 +
        3872020915304169187847625492439606254835728939156477408512419339918591) * 10 ^ 70 +
        6813265136931973159375539127184849181158250030788049800308471810769169) * 10 ^ 70 +
        6170962160596382936395480601816281193793524002728559693552089661109117) * 10 ^ 70 +
        5527385385741648301821080827389955864167899278103575138092538408422614) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 0 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 26 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (165 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_165 :
    recurrence5Scalar0Main.coeff 165 =
      ((((((1698 * 10 ^ 70 +
        7261368150763537141479818678753949231307010353553219521228170365370732) * 10 ^ 70 +
        9065443566487916355779196559167103926972864559558042473415480923507239) * 10 ^ 70 +
        9111961162765749362622664982144330183502024169420351332840470237252234) * 10 ^ 70 +
        7449713032009155181722673470661171121304067270072523766547481546418232) * 10 ^ 70 +
        2506115056535583477086541006888885188770079785523458767452775679051003) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 0 +
    166 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 26 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (166 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_166 :
    recurrence5Scalar0Main.coeff 166 =
      -((((((3660 * 10 ^ 70 +
        2690284089908474027820939439414551999730380863104331650114334528187116) * 10 ^ 70 +
        2160029654675149929890295819041857215919739066076221234826891791752411) * 10 ^ 70 +
        7270966041898162882692302952328638799429385859233579815266120848686870) * 10 ^ 70 +
        5541278392022769364931687865677600777462485607667825934879254751701479) * 10 ^ 70 +
        0730488573698655141900890007666005769905162893230754151277333656958503) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 0 +
    167 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 26 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (167 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_167 :
    recurrence5Scalar0Main.coeff 167 =
      ((((((7747 * 10 ^ 70 +
        4425093265701723738176880476264299776063538041381540263681830797750761) * 10 ^ 70 +
        2524365536124338366705536216366862053915411238987414409661533690160915) * 10 ^ 70 +
        7772088082641753766469716797442900634305547884295100553614777042599635) * 10 ^ 70 +
        6443239736271812569675182788008227053206093107375999550559982679181151) * 10 ^ 70 +
        9795493024409582036197824748798184534498479551065774608560658260445062) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 0 +
    168 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 26 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (168 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_168 :
    recurrence5Scalar0Main.coeff 168 =
      -((((((16109 * 10 ^ 70 +
        6777317493121103767276182017940499238649560575369241494444801062862543) * 10 ^ 70 +
        0401481616719935841314823739599531435347455225950463543208449034536300) * 10 ^ 70 +
        7414194569324465927200397816273654558397320558682621221837846647501190) * 10 ^ 70 +
        9498230683013339357777781979044762916642673131378777333031970125215797) * 10 ^ 70 +
        0633722600436141639456021689163958347645195034159279020776734047042211) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 0 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 26 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (169 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_169 :
    recurrence5Scalar0Main.coeff 169 =
      ((((((32909 * 10 ^ 70 +
        8003780689381898251435128797710030670410762461199660669969719052772820) * 10 ^ 70 +
        9818848356514099005023975930749189542409956603761276848754023715693224) * 10 ^ 70 +
        4967374081330692471185696292344197650520600685307222533698455090933773) * 10 ^ 70 +
        5747486336751911817745982334486848938774759730190766334556334304747389) * 10 ^ 70 +
        6039130843133389205977460378406201515915488402855418373207074695757721) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 0 +
    170 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 26 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (170 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_170 :
    recurrence5Scalar0Main.coeff 170 =
      -((((((66054 * 10 ^ 70 +
        0864775807390685318180736088096274717554580218048772579172626920774978) * 10 ^ 70 +
        5094676413724226923024953565769682417234843316684411106061273464077983) * 10 ^ 70 +
        2746646998525914099548967810227193249034493551858429025397132572668569) * 10 ^ 70 +
        5336162365705026474118258608190798587654272031190647566744779567368145) * 10 ^ 70 +
        0763063851493460880108691087903623904337132563619651269273629217442453) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 0 +
    171 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 26 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (171 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_171 :
    recurrence5Scalar0Main.coeff 171 =
      ((((((130267 * 10 ^ 70 +
        3913966256539621043437875800496066957548915769502625774804978390483892) * 10 ^ 70 +
        2234489698838736458822733880126961765267266935137574944130998113326716) * 10 ^ 70 +
        2481016465368143872051851017560765885810053011622821877954324732851620) * 10 ^ 70 +
        6457782378186851465499363102184723888927972604445198578859892731348683) * 10 ^ 70 +
        0330909873903318339748042876964175799463454972321976560241431644627139) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 0 +
    172 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 26 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (172 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_172 :
    recurrence5Scalar0Main.coeff 172 =
      -((((((252440 * 10 ^ 70 +
        0603940738145149443243754043870910185623804940577351209040268705434706) * 10 ^ 70 +
        3277741411587011767663107184622322147361064756044762596187201381566368) * 10 ^ 70 +
        8747022084191344890000488502375261067070526619188158172535659956689368) * 10 ^ 70 +
        4411258311420139411760869822904553718245374253563558704660294748836715) * 10 ^ 70 +
        9765980561177213392685705121460959000705045217586770876294104579831560) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 0 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 26 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (173 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_173 :
    recurrence5Scalar0Main.coeff 173 =
      ((((((480719 * 10 ^ 70 +
        5142577169503436934773781524434661675859478305328979547493228391079047) * 10 ^ 70 +
        7047433996929225743281154111503660616742161193700422159943204024137869) * 10 ^ 70 +
        7607124057020192143072759129023065706299491028623954990005094221555077) * 10 ^ 70 +
        7227969962241540061043631984312178254356261658155995774415455423759348) * 10 ^ 70 +
        2553296773234705846789830847356398192695122581645356459781262570289512) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 0 +
    174 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 26 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (174 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_174 :
    recurrence5Scalar0Main.coeff 174 =
      -((((((899621 * 10 ^ 70 +
        8328173875776864502580981623873370740160631488353606120352832570244465) * 10 ^ 70 +
        2423683438230815749456045385761691804436577137582040137273384843429708) * 10 ^ 70 +
        3429837375910932786639445168373895926219809079805857354762598912883346) * 10 ^ 70 +
        1010980567824258478543671570373925490572143468987027589972009294760777) * 10 ^ 70 +
        2276382217725118440039809378160668507013629932332261348534015374477641) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 0 +
    175 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 26 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (175 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_175 :
    recurrence5Scalar0Main.coeff 175 =
      ((((((1654574 * 10 ^ 70 +
        3772670136735559528038363260596371532190639510136680384741489986044222) * 10 ^ 70 +
        6712379149950326375201536363846563384845753706028262792430834011107196) * 10 ^ 70 +
        5129466849496170098771578488027760616926060993897602514944006230485020) * 10 ^ 70 +
        9912420708948892571795303530852802785912722433279998611028384721418219) * 10 ^ 70 +
        5476893132656920371353884757578296508821512140551318142941965489054922) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 0 +
    176 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 26 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (176 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_176 :
    recurrence5Scalar0Main.coeff 176 =
      -((((((2990842 * 10 ^ 70 +
        1114477919727829420971290417682013710576363648683563992599600771217339) * 10 ^ 70 +
        1311232830811056999411771352297126478828667777953335241706789473597083) * 10 ^ 70 +
        3351906211484409159382941927092249675993308559003944302009210381549526) * 10 ^ 70 +
        5124338232012783694572477291396783556783412505687842188742619771871207) * 10 ^ 70 +
        2179568038041397144149614877691762407378860992482018292946702502132538) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 0 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 26 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (177 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_177 :
    recurrence5Scalar0Main.coeff 177 =
      ((((((5313783 * 10 ^ 70 +
        9313247921054226750534017391636810636801792396297082428123267939646790) * 10 ^ 70 +
        4888172967344919413304801579849511375377468914967034365155170010525737) * 10 ^ 70 +
        4234336007831389804770771066771265412940708089942206071397301031850465) * 10 ^ 70 +
        0554378617611726959336577169543872999967872350294923694180229682191841) * 10 ^ 70 +
        3083139346252244839814160381599405406483543066209245858564831904954097) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 0 +
    178 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 26 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (178 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_178 :
    recurrence5Scalar0Main.coeff 178 =
      -((((((9279816 * 10 ^ 70 +
        1210117371154704311406919244507088146481258953297823718512654651952350) * 10 ^ 70 +
        4358326132395284608290052605906340379162792512938372363523737191741232) * 10 ^ 70 +
        1061614591791414058054300260094263003093568781957693552403274131083065) * 10 ^ 70 +
        2625531152876176416697326683029192610479444531001791385964746663627113) * 10 ^ 70 +
        1552933663366731171246044052908652823006463378615796458194989870667115) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 0 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (179 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_179 :
    recurrence5Scalar0Main.coeff 179 =
      ((((((15930204 * 10 ^ 70 +
        3000069577704491195638075685411818235617995568025694267625526511667640) * 10 ^ 70 +
        1480079168567054423636234052251116534829237890778258059671091203150139) * 10 ^ 70 +
        8484253910925118818791968237490043865105119744560733114773445638881523) * 10 ^ 70 +
        3940522358652749469906527300386426332028664030332828196775783548003449) * 10 ^ 70 +
        0956200683314767719681006756291699992865174764069971230637494524248783) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 0 +
    180 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 26 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (180 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_180 :
    recurrence5Scalar0Main.coeff 180 =
      -((((((26882571 * 10 ^ 70 +
        6218863391050655589305982500437282966222335788155391536115036106199319) * 10 ^ 70 +
        3834319382695107646155813913722164382082784103487054656952583729583845) * 10 ^ 70 +
        1529436978161162537726350643855361563920793257895614197449190661512275) * 10 ^ 70 +
        4231724159906606735790748999365274673543888613461033787802918314211671) * 10 ^ 70 +
        4173360553558304648711059767272147033067282081907571004605657797210112) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 0 +
    181 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 26 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (181 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_181 :
    recurrence5Scalar0Main.coeff 181 =
      ((((((44597278 * 10 ^ 70 +
        9191128750665671609594600361288277624648636141885818134533764390613992) * 10 ^ 70 +
        9726776892464061662054980319133611318495628877803477618818942553932431) * 10 ^ 70 +
        6697346038983528544500306367434738845153264240855624619468360860286050) * 10 ^ 70 +
        2879169186005902495498657707378880348211574183575431256895953066225064) * 10 ^ 70 +
        6335404515204745394161144403827497646427933961763922745493424078065262) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 0 +
    182 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 26 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (182 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_182 :
    recurrence5Scalar0Main.coeff 182 =
      -((((((72736802 * 10 ^ 70 +
        1026893808564056393505349287954389562623833957826619728530679435584612) * 10 ^ 70 +
        9455540824117407717556096557119188957273026253569486237651496994228403) * 10 ^ 70 +
        5042690054319447331817496878402055523418405238456026626010073694947114) * 10 ^ 70 +
        4469100677551191214775017297226164323428456002053502815598277117026360) * 10 ^ 70 +
        8487493466687483915208919373615558004679736188474563674064719492944474) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 0 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 26 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (183 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_183 :
    recurrence5Scalar0Main.coeff 183 =
      ((((((116634808 * 10 ^ 70 +
        8332007829050746694556317221386424392601606730999201659509403436683455) * 10 ^ 70 +
        8547495759709833884480826536112838056706751606081983368853195341151532) * 10 ^ 70 +
        4174279786586712583783555172408668968246093848993270095630370044186510) * 10 ^ 70 +
        9389178382718845952616681559761124112405581412960513187454005294966476) * 10 ^ 70 +
        9117893206047345709447672985555394799418619585887134045448116106819449) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 0 +
    184 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 26 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (184 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_184 :
    recurrence5Scalar0Main.coeff 184 =
      -((((((183886478 * 10 ^ 70 +
        8631513674498713386405722322867025574989473390925234531838097188992564) * 10 ^ 70 +
        2211557688972659918204188093548398189532367628372293986782652367806657) * 10 ^ 70 +
        3237885635438296100242630580259403267543392146002251807715847100857078) * 10 ^ 70 +
        1740293150110881550526453095471784570060487884346731840026104210831890) * 10 ^ 70 +
        9096140756645182159748212145052160785663051340947497222519493131454232) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 0 +
    185 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 26 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (185 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_185 :
    recurrence5Scalar0Main.coeff 185 =
      ((((((285061274 * 10 ^ 70 +
        1798658407682352063706540230375258630198195979869413744975531374472370) * 10 ^ 70 +
        5128509008375643037265369961385959922153661795125479177991604964021567) * 10 ^ 70 +
        5512542163760076075719767642742956399686122674930506825455869980646863) * 10 ^ 70 +
        3787000065018043726409082159822297933485655899794248676621610329162872) * 10 ^ 70 +
        7847864519243492237784574100677099398141780336173360483548895587694671) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 0 +
    186 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 26 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (186 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_186 :
    recurrence5Scalar0Main.coeff 186 =
      -((((((434522554 * 10 ^ 70 +
        9206460507254485652572058209685015399102806695113995547296870731664923) * 10 ^ 70 +
        4697022836649865894241830293648373922413915292643275133271479123644039) * 10 ^ 70 +
        5797355343620714460482460311206173338009730097064624907808973623319387) * 10 ^ 70 +
        1698765557043769089692479547872047774456939501758816440305992850295875) * 10 ^ 70 +
        6164491984518248431587463818111561606779250619092734596879904618280185) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 0 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 26 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (187 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_187 :
    recurrence5Scalar0Main.coeff 187 =
      ((((((651314402 * 10 ^ 70 +
        7113126651999240876360626746595816881839666147528348976931956807627082) * 10 ^ 70 +
        0649694351583103576486753807236611465220350283723191930291341938771991) * 10 ^ 70 +
        5683990271681692997862699134353867367906623160526286088438662099989052) * 10 ^ 70 +
        2900271934897147865776696553812846525115515063458270487154360223887374) * 10 ^ 70 +
        9234561680041995929070945594829330426911896292503747459571957240825511) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 0 +
    188 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 26 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (188 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_188 :
    recurrence5Scalar0Main.coeff 188 =
      -((((((960045023 * 10 ^ 70 +
        2320393054855685170690568342610231279410675418157070584046378329071095) * 10 ^ 70 +
        0638819205504431504759397838973516944216029240535061465771411693951827) * 10 ^ 70 +
        4963297894821052969814014494842876430689172387098852959234987263785631) * 10 ^ 70 +
        7830622398407946452418249475248125161905882097203645031627758640566048) * 10 ^ 70 +
        4006628869693690726851831471189181772094613441165310140725690715956998) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 0 +
    189 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 26 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (189 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_189 :
    recurrence5Scalar0Main.coeff 189 =
      ((((((1391659955 * 10 ^ 70 +
        5798457869299522346153945795551786539850045831907675473099260686553356) * 10 ^ 70 +
        8872718841244190594122800400330478581459808502950742315567959800763937) * 10 ^ 70 +
        9873239983462027085099209446039124402403524632085826623841508930216978) * 10 ^ 70 +
        2932901866585460021597582571459446692578597613305323086469816796054856) * 10 ^ 70 +
        0851787828880033993784872137819751679064427269933172786974595138654478) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 0 +
    190 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 26 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (190 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_190 :
    recurrence5Scalar0Main.coeff 190 =
      -((((((1983960776 * 10 ^ 70 +
        9540785511416465078179514189601926899068097477413712400691870732818189) * 10 ^ 70 +
        3405807560708880145940086088227321927888850021527890771174012635835453) * 10 ^ 70 +
        1101896117788519390154839189510573078184748572929342332039027430838893) * 10 ^ 70 +
        5978409246570663595110267267079354894642956785646582827218172125358146) * 10 ^ 70 +
        5584387718160611644473561138773623263064657583622415054420225097850924) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 0 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 26 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (191 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_191 :
    recurrence5Scalar0Main.coeff 191 =
      ((((((2781691961 * 10 ^ 70 +
        8476318666373975889911501561310926444937336724686726483242285568777224) * 10 ^ 70 +
        6170676200072209776555981618260977545383482064923057751381230987058868) * 10 ^ 70 +
        4265628018916886211071795099341686168476364397782542838158261029352060) * 10 ^ 70 +
        3479248851035750472837871565821960440605621627621418231809683956957388) * 10 ^ 70 +
        5198897073357225582340857812092330131235093780912684230462666991268009) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 0 +
    192 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 26 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (192 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_192 :
    recurrence5Scalar0Main.coeff 192 =
      -((((((3835997864 * 10 ^ 70 +
        2500292694691390518265412756493096329074842811757088852109575955933367) * 10 ^ 70 +
        6342059946844157963686553662599207837085859314740712405531236122331948) * 10 ^ 70 +
        7875755790761096799668593852833307968488044736422469047955045460057225) * 10 ^ 70 +
        9618464913029593962147920743271268277597366474456434480192700014971641) * 10 ^ 70 +
        3385021309752150262896661587790154012131676317031982567761917236470428) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 0 +
    193 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 26 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (193 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_193 :
    recurrence5Scalar0Main.coeff 193 =
      ((((((5203052425 * 10 ^ 70 +
        7468339977807102743772349701678237464406758163821339025949751507421419) * 10 ^ 70 +
        9572731257059892284469010551741034148601014137682165782947076318523269) * 10 ^ 70 +
        5968778676335996116161786808470508637731328589168947209211281215163084) * 10 ^ 70 +
        5137649056633937624492068493310426080969563398964196954436648573267741) * 10 ^ 70 +
        0820922514650706566362587203643714415925476761519616827376753545724103) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 0 +
    194 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 26 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (194 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_194 :
    recurrence5Scalar0Main.coeff 194 =
      -((((((6941694943 * 10 ^ 70 +
        5432303003255080682736858801653305088169965958716036244720192447594738) * 10 ^ 70 +
        2905479777340016826906349955305548153506437483555726674914425938227708) * 10 ^ 70 +
        5218307657617456359236710946009654354120595471649826382471151690906488) * 10 ^ 70 +
        7141562669390102276460317577575650667763360897871481464512534137765677) * 10 ^ 70 +
        0718471813023150540190794988752375902912623893675583002650347675551453) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 0 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 26 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (195 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_195 :
    recurrence5Scalar0Main.coeff 195 =
      ((((((9109972715 * 10 ^ 70 +
        9377280967767063637412835641654395105808259205394657433326554389051111) * 10 ^ 70 +
        8377101912881880973385440842158280491806373286113140123365930920020382) * 10 ^ 70 +
        9794776155341013851235246695883101399513234335265843555082724047585464) * 10 ^ 70 +
        5747797593625070921168587865167891020724460170034068214093654513812473) * 10 ^ 70 +
        7688059506908251647694031259002399643653462734216906139806354743429167) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 0 +
    196 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 26 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (196 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_196 :
    recurrence5Scalar0Main.coeff 196 =
      -((((((11760597973 * 10 ^ 70 +
        1629869569889769715859142440617397193755353014843987194923671346964611) * 10 ^ 70 +
        8876646949975140328254704253229267551247503167477094429281495059617312) * 10 ^ 70 +
        5337434694452397263068045449837410787831232576086282681667435580765641) * 10 ^ 70 +
        4991677290137865627303989472289896711656108395296392158252265806103432) * 10 ^ 70 +
        3938451645444624660276629795641786081391996331971549124758224900263477) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 0 +
    197 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (197 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_197 :
    recurrence5Scalar0Main.coeff 197 =
      ((((((14935468200 * 10 ^ 70 +
        0182658516762616783791609061359414802959919133947120788442937918781369) * 10 ^ 70 +
        5848581092066010904782313874189177111733511338703442188680641193832752) * 10 ^ 70 +
        3566117631443562401075157206336410686963296761037410549584162302777524) * 10 ^ 70 +
        5651126881114783716499899453817986176584531078765438111096941582686354) * 10 ^ 70 +
        7517262748706263109154501166037179767132076558875648613782942439534607) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 0 +
    198 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 26 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (198 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_198 :
    recurrence5Scalar0Main.coeff 198 =
      -((((((18659564028 * 10 ^ 70 +
        1779975941769657416753955689529234047228205617988542615869612001090043) * 10 ^ 70 +
        7765508018205373791292432982489391505599925614016996213943628608839250) * 10 ^ 70 +
        3698705037296129497106301813285096703936131015850249651503772121487590) * 10 ^ 70 +
        5695696810868387196451754654556630762305919496943782196868142524110131) * 10 ^ 70 +
        1818641211382356824265936927213044722488103316471536753066897212265685) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 0 +
    199 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 26 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (199 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_199 :
    recurrence5Scalar0Main.coeff 199 =
      ((((((22934707688 * 10 ^ 70 +
        5349196073109731510667989756361660632399500571528203498344808142238759) * 10 ^ 70 +
        6797628494985458888307701992165990210990845892453895760917052612491325) * 10 ^ 70 +
        9455507592992760499580722298831417551274127898608382314071494558025439) * 10 ^ 70 +
        0485235572986968643679178488276947696709348714438905484722360032830998) * 10 ^ 70 +
        6309456587934561933277971999252466637167791700437760112940936913214577) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 0 +
    200 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 26 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (200 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_200 :
    recurrence5Scalar0Main.coeff 200 =
      -((((((27733811527 * 10 ^ 70 +
        5018790559010070670062984359833082688908915625641808260597678850329821) * 10 ^ 70 +
        0983858636439097687129728581505869314620535275032263109239471360331231) * 10 ^ 70 +
        5487775346580469647463767194262517729977069536197560582841487209050243) * 10 ^ 70 +
        4177233092892616073430581083072811289419590710427472819638185162659968) * 10 ^ 70 +
        9413594395223804315495963319493570658331978670831538602753704512700446) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 0 +
    201 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 26 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (201 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_201 :
    recurrence5Scalar0Main.coeff 201 =
      ((((((32996341141 * 10 ^ 70 +
        2339543527427671384174524840915363193018997067018082089799566359800557) * 10 ^ 70 +
        4206730578340095199483330796849159387653109283346385552519803233288490) * 10 ^ 70 +
        7796746299629967401477737611554840194062824488842619604558838732954248) * 10 ^ 70 +
        0337781746757087677764966161074503269342458546036052458493204460105121) * 10 ^ 70 +
        6556159327503088788694429809767296806035397172567734573560167498969717) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 0 +
    202 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 26 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (202 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_202 :
    recurrence5Scalar0Main.coeff 202 =
      -((((((38625733799 * 10 ^ 70 +
        8599372590483812506670487190637036847602778940522406080061187631121506) * 10 ^ 70 +
        9733024985456762805318867706498186136797432872595301530443923642154151) * 10 ^ 70 +
        5816104242129127878782483038382591293035326380566779961534177894190516) * 10 ^ 70 +
        1744218991956416321586441876993247884377232296361047043259456163927558) * 10 ^ 70 +
        9349777682371140861198686382375707769484694183024908360724787226215326) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 0 +
    203 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 26 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (203 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_203 :
    recurrence5Scalar0Main.coeff 203 =
      ((((((44489429905 * 10 ^ 70 +
        4661359166256716011374628224679980928371476349564878918868538431541417) * 10 ^ 70 +
        7623877783565746137260864731759442694921499450283227561625965413937992) * 10 ^ 70 +
        8620733813422633002281841676019852167860196828615407203616227739280122) * 10 ^ 70 +
        9430125522867448507743005970015926660126531950999213042586455914713476) * 10 ^ 70 +
        6814618284990831549947269880898009334984416586444406189222664314082326) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 0 +
    204 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 26 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (204 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_204 :
    recurrence5Scalar0Main.coeff 204 =
      -((((((50421985911 * 10 ^ 70 +
        7572810599417175791840339228577855971719627714857713527551705297526701) * 10 ^ 70 +
        6965397200456302823512832765067268721835703092060446121361706837959834) * 10 ^ 70 +
        8258322835978910006776567121156506831029533382306469379056329119233610) * 10 ^ 70 +
        6159956815446854372283177715395207061742877073290405124572692935972680) * 10 ^ 70 +
        0846031033367232845622296605827478540123346616428357308406026747846386) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 0 +
    205 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 26 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (205 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_205 :
    recurrence5Scalar0Main.coeff 205 =
      ((((((56231450787 * 10 ^ 70 +
        1735292859671313619604316859386540331194182695114248302944785843723401) * 10 ^ 70 +
        1448911758567682762687728404223699470174757262535615069812290641196539) * 10 ^ 70 +
        9375441178006603869273933676121132542199108350694983723770909564841162) * 10 ^ 70 +
        8799188395719172012159153790453933218026012115983463960322352652069382) * 10 ^ 70 +
        8336283265147137622058533439363539968005511089685270903134147859376874) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 0 +
    206 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 26 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (206 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_206 :
    recurrence5Scalar0Main.coeff 206 =
      -((((((61708832053 * 10 ^ 70 +
        7869171621819384597618546644400455924110648297565665206361845673886070) * 10 ^ 70 +
        1061589876209430229544794447108064762291191843651317485873234059339604) * 10 ^ 70 +
        1338583822364021210749230922816962836780147173240966304542137781592789) * 10 ^ 70 +
        7557730798358580307719848943791246495739006142574567928932152699138449) * 10 ^ 70 +
        4603176660597239618741209946980545122689766775809630820135899687337239) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 0 +
    207 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 26 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (207 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_207 :
    recurrence5Scalar0Main.coeff 207 =
      ((((((66640094851 * 10 ^ 70 +
        4317390173859526577016798903028724278463164483421938166421164237021942) * 10 ^ 70 +
        6238616969505851665264225366616683004747892549841583671321273395669136) * 10 ^ 70 +
        6481796867104640345332571473753772978328643661258511848638245889972277) * 10 ^ 70 +
        0268497241884009227827692874245653869892528705984989041469752432587040) * 10 ^ 70 +
        7226078285848133810071119462321908172140634528348408121238242630133026) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 0 +
    208 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 26 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (208 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_208 :
    recurrence5Scalar0Main.coeff 208 =
      -((((((70819781771 * 10 ^ 70 +
        4999814306525591224694905249429449710838509791815814292380798628175526) * 10 ^ 70 +
        6395103377430846677544570174744528131398937725172185177229648110820953) * 10 ^ 70 +
        9370984269995871860666894073761177511663222579312647178633433517580627) * 10 ^ 70 +
        9122513132744042599318653873683048120445639409528953321208410379287696) * 10 ^ 70 +
        5199054851073369307512281237417490784516041943087393318892905203352347) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 0 +
    209 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 26 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (209 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_209 :
    recurrence5Scalar0Main.coeff 209 =
      ((((((74065067670 * 10 ^ 70 +
        6878023021084255362704059207117144545730671567569699510904607811013974) * 10 ^ 70 +
        0686795175913282406377451482463638476701991504996072328112550507640916) * 10 ^ 70 +
        3891420074698151240834079501882267952869224214209330935156006052290468) * 10 ^ 70 +
        8031313419113190314453619834551774948912752004287187084193495626765388) * 10 ^ 70 +
        2042261910334551650722964022397988485174330212987999790205896636728169) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 0 +
    210 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 26 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (210 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_210 :
    recurrence5Scalar0Main.coeff 210 =
      -((((((76228919808 * 10 ^ 70 +
        7906569514193379872022043450289347185505419984027964944479267239581878) * 10 ^ 70 +
        9165486435479827594701172638192122704866481532267987640561592156588502) * 10 ^ 70 +
        8965147150497122480262583221674163715639726935662012007146443736755251) * 10 ^ 70 +
        1474591675918449857301072819349565044831054470114974840994916153410320) * 10 ^ 70 +
        8524766249755612254966128744575184747500216901785086343677294283182868) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 0 +
    211 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 26 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (211 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_211 :
    recurrence5Scalar0Main.coeff 211 =
      ((((((77211050059 * 10 ^ 70 +
        1320354060135732266999534079555366350324614686877133973849700373770434) * 10 ^ 70 +
        4914009571384168512412242693819234931879241884332353398883226987971824) * 10 ^ 70 +
        1545719478339306060892493019716983163607147413545135916875474575792624) * 10 ^ 70 +
        9627499990141348219213297122467358318343551142217240587599538224167475) * 10 ^ 70 +
        6301046596309525584701184219964081951334218173751373090174728137272670) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 0 +
    212 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 26 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (212 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_212 :
    recurrence5Scalar0Main.coeff 212 =
      -((((((76965529747 * 10 ^ 70 +
        1049384401742903682059225742961076403913406116805610821201651764447223) * 10 ^ 70 +
        3205058022879275735102912554797151412125118664817850785769124052059037) * 10 ^ 70 +
        6546747481946962589554499844683837594634334383266291441653397094134617) * 10 ^ 70 +
        9201194101383739170300501598479239505852407216514578387599560820977446) * 10 ^ 70 +
        8503236965247033827880817000895666072393340240978289569537371481024244) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 0 +
    213 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 26 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (213 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_213 :
    recurrence5Scalar0Main.coeff 213 =
      ((((((75504270014 * 10 ^ 70 +
        1319488950564791784808537312247557738494916257824167577447865098084894) * 10 ^ 70 +
        3726521962816198263971075425232007823175151287192873102890723546742359) * 10 ^ 70 +
        0933970698380669344100881729047116362846534678726391950526746419162911) * 10 ^ 70 +
        2142302214024016519048342765775313044685259595013873677110572277491155) * 10 ^ 70 +
        5723409238802633455183465745571862000545299607203338710544947988959023) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 0 +
    214 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 26 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (214 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_214 :
    recurrence5Scalar0Main.coeff 214 =
      -((((((72896008857 * 10 ^ 70 +
        0102292880488131881226550056566304247297310055190470463173044317416561) * 10 ^ 70 +
        5140426499324477767799785288143168791788937358000210593679612386842763) * 10 ^ 70 +
        1920327412243112511254769863955124496979784422773756354738445280399640) * 10 ^ 70 +
        6391188776921609014351477024748597926500413617207289408416757580661311) * 10 ^ 70 +
        1100281542591381537095005656823207877064302652547926850719739548781244) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 0 +
    215 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 26 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (215 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_215 :
    recurrence5Scalar0Main.coeff 215 =
      ((((((69260930499 * 10 ^ 70 +
        2698232306945177915857311651579591138833780955000825418324182518895312) * 10 ^ 70 +
        9675356256706279517015590071113667596983000970895302385541341321089906) * 10 ^ 70 +
        4326559434398271804273010740455870041449442570440115900993000516751201) * 10 ^ 70 +
        8293040432427525701374221122832547962319133545735191062075603189289717) * 10 ^ 70 +
        2427956581587957747259291860408531911503171348853268232877210214833856) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 0 +
    216 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 26 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (216 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_216 :
    recurrence5Scalar0Main.coeff 216 =
      -((((((64761506762 * 10 ^ 70 +
        3768725608156183577610256432198358979090767286733593629873901095012708) * 10 ^ 70 +
        0386195054186685735479950010259994917871225470463054592210971798137004) * 10 ^ 70 +
        4875276691374950566019479902147922939748696270036940614463365714027738) * 10 ^ 70 +
        3705485309971988208776756116925027635977139949181632600405214001271339) * 10 ^ 70 +
        4997598694379988502122595386312108192083403432604809575118583471169442) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 0 +
    217 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 26 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (217 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_217 :
    recurrence5Scalar0Main.coeff 217 =
      ((((((59590530971 * 10 ^ 70 +
        2563172895542756633154780149861204056081079323327563346699429287299149) * 10 ^ 70 +
        9736473662787785805934112590899434394072565341305884502251148413132878) * 10 ^ 70 +
        2290734613603647302254602133482779001374466168450077288242867332545102) * 10 ^ 70 +
        4128277040716629907664768126823908061498611235988830952991703572252483) * 10 ^ 70 +
        3471608569235133059139187193227700843373112955805673212312088107642447) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 0 +
    218 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 26 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (218 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_218 :
    recurrence5Scalar0Main.coeff 218 =
      -((((((53957564335 * 10 ^ 70 +
        2104043479646240767783526203653895283245040561895552119938920752224486) * 10 ^ 70 +
        9685441352019577398783224469846776223682022455320472111377313502651236) * 10 ^ 70 +
        7483071983296916847643611135078848475526826523962229305048236196516457) * 10 ^ 70 +
        9260860532070975126430088276149939811153566040161081609747187363165830) * 10 ^ 70 +
        5524883271267583312267546360180603608109193150478132282508431963819475) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 0 +
    219 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 26 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (219 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_219 :
    recurrence5Scalar0Main.coeff 219 =
      ((((((48075106025 * 10 ^ 70 +
        5462679799130728439007005226515808841026514386150984457843044164680727) * 10 ^ 70 +
        9402421347943522039167610734533469267264721991388645294220479523954145) * 10 ^ 70 +
        6250990647211263216973704227181320554633745276587468754351302415753317) * 10 ^ 70 +
        2467336769352425591128747643815461168060866242168547907533136035475679) * 10 ^ 70 +
        8464394607151184690797539742966660692791593399298100967277459942810427) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 0 +
    220 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 26 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (220 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_220 :
    recurrence5Scalar0Main.coeff 220 =
      -((((((42145729431 * 10 ^ 70 +
        2819202515049645461421278816299566794505594560484025157572982854511388) * 10 ^ 70 +
        0551058846723654789433957991928780853933639273436809883580961360837385) * 10 ^ 70 +
        7458322333006368453491285503369062359396656240964970022682571346019157) * 10 ^ 70 +
        4184869245051246802817421732267368065286459240498578009298557353763324) * 10 ^ 70 +
        5856150407665413515689411482789253326402733709710497385120107620951545) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 0 +
    221 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 26 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar0Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (221 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_221 :
    recurrence5Scalar0Main.coeff 221 =
      ((((((36351219781 * 10 ^ 70 +
        3410869271258315287727493336962757635500039015111691085221046463250053) * 10 ^ 70 +
        7429753640817540685089391439377752578877904598613147843414037563497935) * 10 ^ 70 +
        4943438671048146814582911812429730274290683139602201131064442049517544) * 10 ^ 70 +
        6325917985509709282038339522786458895432914056804081117183135039128333) * 10 ^ 70 +
        6360735023874071860201486321011258264298148071337396540845527309469357) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 0 +
    222 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 26 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
