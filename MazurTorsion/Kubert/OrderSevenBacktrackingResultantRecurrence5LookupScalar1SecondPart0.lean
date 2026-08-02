/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B1_coeff_0
  recurrence5B1_coeff_1
  recurrence5B1_coeff_2
  recurrence5B1_coeff_3
  recurrence5B1_coeff_4
  recurrence5B1_coeff_5
  recurrence5B1_coeff_6
  recurrence5B1_coeff_7
  recurrence5B1_coeff_8
  recurrence5B1_coeff_9
  recurrence5B1_coeff_10
  recurrence5B1_coeff_11
  recurrence5B1_coeff_12
  recurrence5B1_coeff_13
  recurrence5B1_coeff_14
  recurrence5B1_coeff_15
  recurrence5B1_coeff_16
  recurrence5B1_coeff_17
  recurrence5B1_coeff_18
  recurrence5B1_coeff_19
  recurrence5B1_coeff_20
  recurrence5B1_coeff_21
  recurrence5B1_coeff_22
  recurrence5B1_coeff_23
  recurrence5B1_coeff_24
  recurrence5B1_coeff_25
  recurrence5B1_coeff_26
  recurrence5B1_coeff_27
  recurrence5B1_coeff_28
  recurrence5B1_coeff_29
  recurrence5B1_coeff_30
  recurrence5B1_coeff_31
  recurrence5B1_coeff_32
  recurrence5B1_coeff_33
  recurrence5B1_coeff_34
  recurrence5B1_coeff_35
  recurrence5B1_coeff_36
  recurrence5B1_coeff_37
  recurrence5B1_coeff_38
  recurrence5B1_coeff_39
  recurrence5B1_coeff_40
  recurrence5B1_coeff_41
  recurrence5B1_coeff_42
  recurrence5B1_coeff_43
  recurrence5B1_coeff_44
  recurrence5B1_coeff_45
  recurrence5B1_coeff_46
  recurrence5B1_coeff_47
  recurrence5B1_coeff_48
  recurrence5B1_coeff_49
  recurrence5B1_coeff_50
  recurrence5B1_coeff_51
  recurrence5B1_coeff_52
  recurrence5B1_coeff_53
  recurrence5B1_coeff_54
  recurrence5B1_coeff_55
  recurrence5B1_coeff_56
  recurrence5B1_coeff_57
  recurrence5B1_coeff_58
  recurrence5B1_coeff_59
  recurrence5B1_coeff_60
  recurrence5B1_coeff_61
  recurrence5B1_coeff_62
  recurrence5B1_coeff_63

attribute [local simp]
  recurrence5B1_coeff_64
  recurrence5B1_coeff_65
  recurrence5B1_coeff_66
  recurrence5B1_coeff_67
  recurrence5B1_coeff_68
  recurrence5B1_coeff_69
  recurrence5B1_coeff_70
  recurrence5B1_coeff_71
  recurrence5B1_coeff_72
  recurrence5B1_coeff_73
  recurrence5B1_coeff_74
  recurrence5B1_coeff_75
  recurrence5B1_coeff_76
  recurrence5B1_coeff_77
  recurrence5B1_coeff_78
  recurrence5B1_coeff_79
  recurrence5B1_coeff_80
  recurrence5B1_coeff_81
  recurrence5B1_coeff_82
  recurrence5B1_coeff_83
  recurrence5B1_coeff_84
  recurrence5B1_coeff_85
  recurrence5B1_coeff_86
  recurrence5B1_coeff_87
  recurrence5B1_coeff_88
  recurrence5B1_coeff_89
  recurrence5B1_coeff_90
  recurrence5B1_coeff_91
  recurrence5B1_coeff_92
  recurrence5B1_coeff_93
  recurrence5B1_coeff_94
  recurrence5B1_coeff_95
  recurrence5B1_coeff_96
  recurrence5B1_coeff_97
  recurrence5B1_coeff_98
  recurrence5B1_coeff_99
  recurrence5B1_coeff_100
  recurrence5B1_coeff_101
  recurrence5B1_coeff_102
  recurrence5B1_coeff_103
  recurrence5B1_coeff_104
  recurrence5B1_coeff_105
  recurrence5B1_coeff_106
  recurrence5B1_coeff_107
  recurrence5B1_coeff_108
  recurrence5B1_coeff_109
  recurrence5B1_coeff_110
  recurrence5B1_coeff_111
  recurrence5B1_coeff_112
  recurrence5B1_coeff_113
  recurrence5B1_coeff_114
  recurrence5B1_coeff_115
  recurrence5B1_coeff_116
  recurrence5B1_coeff_117
  recurrence5B1_coeff_118
  recurrence5B1_coeff_119
  recurrence5B1_coeff_120
  recurrence5B1_coeff_121
  recurrence5B1_coeff_122
  recurrence5B1_coeff_123
  recurrence5B1_coeff_124
  recurrence5B1_coeff_125
  recurrence5B1_coeff_126
  recurrence5B1_coeff_127

attribute [local simp]
  recurrence5B1_coeff_128
  recurrence5B1_coeff_129
  recurrence5B1_coeff_130
  recurrence5B1_coeff_131
  recurrence5B1_coeff_132
  recurrence5B1_coeff_133
  recurrence5B1_coeff_134
  recurrence5B1_coeff_135
  recurrence5B1_coeff_136
  recurrence5B1_coeff_137
  recurrence5B1_coeff_138
  recurrence5B1_coeff_139
  recurrence5B1_coeff_140
  recurrence5B1_coeff_141
  recurrence5B1_coeff_142
  recurrence5B1_coeff_143
  recurrence5B1_coeff_144
  recurrence5B1_coeff_145
  recurrence5B1_coeff_146
  recurrence5B1_coeff_147
  recurrence5B1_coeff_148
  recurrence5B1_coeff_149
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
  recurrence5QuotientConstant_coeff_38
  recurrence5QuotientConstant_coeff_39
  recurrence5QuotientConstant_coeff_40
  recurrence5QuotientConstant_coeff_41

attribute [local simp]
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
  recurrence5QuotientConstant_coeff_102
  recurrence5QuotientConstant_coeff_103
  recurrence5QuotientConstant_coeff_104
  recurrence5QuotientConstant_coeff_105

attribute [local simp]
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
  recurrence5QuotientConstant_coeff_166
  recurrence5QuotientConstant_coeff_167
  recurrence5QuotientConstant_coeff_168
  recurrence5QuotientConstant_coeff_169

attribute [local simp]
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
  recurrence5QuotientConstant_coeff_230
  recurrence5QuotientConstant_coeff_231
  recurrence5QuotientConstant_coeff_232
  recurrence5QuotientConstant_coeff_233

attribute [local simp]
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
  recurrence5QuotientConstant_coeff_294
  recurrence5QuotientConstant_coeff_295
  recurrence5QuotientConstant_coeff_296
  recurrence5QuotientConstant_coeff_297

attribute [local simp]
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

theorem recurrence5Scalar1Second_coeff_0 :
    recurrence5Scalar1Second.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_1 :
    recurrence5Scalar1Second.coeff 1 =
      -((874329999230354856949778724713671756358685839545836632 * 10 ^ 70 +
        5678569564305562648536750290905804166301263084797303351258570103619584) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_2 :
    recurrence5Scalar1Second.coeff 2 =
      ((2541983299061609936205587251996988085013171561525651398469 * 10 ^ 70 +
        7968291606782825385315783725771023124545444820599989894514004641286144) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_3 :
    recurrence5Scalar1Second.coeff 3 =
      ((41499569849130188502025134369838307064436167340712968730960743 * 10 ^ 70 +
        4992151763815263001242197692872935566288697717371425866198766553784448) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_4 :
    recurrence5Scalar1Second.coeff 4 =
      -((373866489416215039959015917776978985067138483737492422183753890699 * 10 ^ 70 +
        6082805030848852508947727607677484136636195814021358718858023957615008) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_5 :
    recurrence5Scalar1Second.coeff 5 =
      ((1578828268042880376205472207618022168157311435679658476081437901191052 * 10 ^ 70 +
        4397728542400807567975531977217616829982429230486795903168304551075328) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_6 :
    recurrence5Scalar1Second.coeff 6 =
      -(((431 * 10 ^ 70 +
        1580125155019361918621088047545182236750970936441279395323362585060030) * 10 ^ 70 +
        5177851753959272768786494055674110844414209221894046704614308852712088) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_7 :
    recurrence5Scalar1Second.coeff 7 =
      (((847559 * 10 ^ 70 +
        4175982646017875507780091715756578537518103252815577775702449228308856) * 10 ^ 70 +
        8385916010355965014155171465711776514823828681675159441238646052125576) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_8 :
    recurrence5Scalar1Second.coeff 8 =
      -(((1250611081 * 10 ^ 70 +
        7209687065112312159012741144968458439225650025805386414748901297652659) * 10 ^ 70 +
        5746683526102255424471891548690152298533798191811916204698640065493960) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_9 :
    recurrence5Scalar1Second.coeff 9 =
      (((1384412024128 * 10 ^ 70 +
        8575835154266485691467486545302120660013822922241655450321894368590186) * 10 ^ 70 +
        1744729011204025290472220489405618615505165520902187675634681179080984) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_10 :
    recurrence5Scalar1Second.coeff 10 =
      -(((1104937455495461 * 10 ^ 70 +
        3725861826205024034825576914375802732949053051755877349318456736679204) * 10 ^ 70 +
        2130381354674347819062162339679320585380436603612494339933692237516248) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_11 :
    recurrence5Scalar1Second.coeff 11 =
      (((556822979855681293 * 10 ^ 70 +
        6101540128663363143300872528834512351648003424716540008928962210289001) * 10 ^ 70 +
        5156801194589886574808536012161213447827695990008333842434130317798036) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_12 :
    recurrence5Scalar1Second.coeff 12 =
      -(((60575234819544107175 * 10 ^ 70 +
        5081855308158397747945650585968827101630495577999531900254833286518511) * 10 ^ 70 +
        3574751678628345087792912254874043320306944044756033726048817522383236) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_13 :
    recurrence5Scalar1Second.coeff 13 =
      -(((176324212871280807502873 * 10 ^ 70 +
        6797575298693895047844397887481688300605184278930747658968302240111299) * 10 ^ 70 +
        9252623803585441183284235021851648606982145515352162358339777846266752) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_14 :
    recurrence5Scalar1Second.coeff 14 =
      (((181380900707500678193745648 * 10 ^ 70 +
        2209907289545733805436451056108593757916293751182324567691860252089662) * 10 ^ 70 +
        6944985287437015357713447296228071486381449386150134544997730917682556) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_15 :
    recurrence5Scalar1Second.coeff 15 =
      -(((97339493149672560056843609946 * 10 ^ 70 +
        3376672881442915952464442330235873039210887391602296762479374498263933) * 10 ^ 70 +
        8344836716394895913047882985023509920201830056118808452072261595997060) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_16 :
    recurrence5Scalar1Second.coeff 16 =
      (((28392577886670106597954340217794 * 10 ^ 70 +
        4632770880740739356738838873291151075850482036256746824833656407529829) * 10 ^ 70 +
        6331872431600329087072203593178422604971962278626616664915704215042842) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_17 :
    recurrence5Scalar1Second.coeff 17 =
      (((684280018633407583129115962821304 * 10 ^ 70 +
        4254120481127974155901580612677847175216933937966263926526120183236799) * 10 ^ 70 +
        3829479248075277507306243379921222934273101289494244549775993003577154) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_18 :
    recurrence5Scalar1Second.coeff 18 =
      -(((5496914147806264244339931710145827656 * 10 ^ 70 +
        0087312878721817593246180251744316386303143837898475788892876452976347) * 10 ^ 70 +
        0583839119732080635865810645698752214845476733168112761929051659043050) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_19 :
    recurrence5Scalar1Second.coeff 19 =
      (((3198032443077769730022180032133230173479 * 10 ^ 70 +
        0884554593837505057727303829868312402791586498178368227794943283010452) * 10 ^ 70 +
        5955406022920501713994566289727713328053528454275109728487820035967136) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_20 :
    recurrence5Scalar1Second.coeff 20 =
      -(((1101406338240170038243404714338243586829540 * 10 ^ 70 +
        1832121826996460756347951025293116366590333903853976716355402858330593) * 10 ^ 70 +
        8112333807748181540481812185193835069793183720425765682352523480423590) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_21 :
    recurrence5Scalar1Second.coeff 21 =
      (((256595608904217850933753954516056741833773060 * 10 ^ 70 +
        8928951417753842604608282792400506371977071479288274256001407429751071) * 10 ^ 70 +
        3736644111117953342921314787519709779917727550828526483745995462261667) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_22 :
    recurrence5Scalar1Second.coeff 22 =
      -(((51968581238840044491877107465056547110096616974 * 10 ^ 70 +
        7181755636113912915031302268347843693827289934951869917133329259787359) * 10 ^ 70 +
        0193654407328425162457895792592295607127779797834377974666161133117431) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_23 :
    recurrence5Scalar1Second.coeff 23 =
      (((22718004181530281859006480478334634423497043496391 * 10 ^ 70 +
        6338123002799261530168686322830937294998280904755964523761224761619987) * 10 ^ 70 +
        8451110985463824897424944440491463982134293130616362312815869867765202) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_24 :
    recurrence5Scalar1Second.coeff 24 =
      -(((15999864124184554369577265392463053588538243670008926 * 10 ^ 70 +
        5000547616470339610334469328558088789586840055642948870216607894562620) * 10 ^ 70 +
        1754312886071134153051538086623652310809628021621282888479435413609520) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_25 :
    recurrence5Scalar1Second.coeff 25 =
      (((9089850459894996914328003773592590323738015217473293970 * 10 ^ 70 +
        4365141560541407730753830507722001438360264432753058533541915198003332) * 10 ^ 70 +
        4025450869044816023469613241345400244417489739450695299833080286424693) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_26 :
    recurrence5Scalar1Second.coeff 26 =
      -(((3967848341612239854749724697968114771293453285565404510848 * 10 ^ 70 +
        0606347050586650997354551457690486776957982917322488181794200398587332) * 10 ^ 70 +
        3569236625530467092265768037616909318717603868016657633803245456851018) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_27 :
    recurrence5Scalar1Second.coeff 27 =
      (((1393912400661866901444940363365267715065908023088339570118889 * 10 ^ 70 +
        2616796756545751480085444724152814479928988553622944224894043187123428) * 10 ^ 70 +
        4493433125444468147120581291282771666780087745570114483744340259330326) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_28 :
    recurrence5Scalar1Second.coeff 28 =
      -(((408275630222538699458773726149118744296164080531740508845868256 * 10 ^ 70 +
        4497429974255035208207406766707739525964035448726354981779120330203570) * 10 ^ 70 +
        1153041405033633294774548265253441891333503213581462716038859050625194) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_29 :
    recurrence5Scalar1Second.coeff 29 =
      (((101900862608278334030785577212485796878952996363692382796904539342 * 10 ^ 70 +
        2123612506231911930844521296993135004567817915653497527956099410918399) * 10 ^ 70 +
        2730315180658592452420555488724185035913248592659486166134263734292159) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_30 :
    recurrence5Scalar1Second.coeff 30 =
      -(((21936491393138852683989599985153557914708729710270423336305574463208 * 10 ^ 70 +
        5735424068351369633312305397133024404212709592564351366956413220347727) * 10 ^ 70 +
        0988933544071056718388023097090399664966520101824125153125916662969068) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_31 :
    recurrence5Scalar1Second.coeff 31 =
      (((4090363314043664563223668320185828636745647970201500182881041816828676 * 10 ^ 70 +
        9408849853689694788065404228766758420524536197681103609386053128724771) * 10 ^ 70 +
        8078787418701758979025334620838864678928076712740856066858151780097838) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_32 :
    recurrence5Scalar1Second.coeff 32 =
      -((((65 * 10 ^ 70 +
        7636931256756034009056378226832524502168121691527520952321379232745394) * 10 ^ 70 +
        4411589211605886820903994077601024728564974425220196127427243234572530) * 10 ^ 70 +
        2480521001615197886197529401443950505439636496534334734668678420404037) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_33 :
    recurrence5Scalar1Second.coeff 33 =
      ((((8943 * 10 ^ 70 +
        6199959083517355769945063942304574896392897344720479004597326257352705) * 10 ^ 70 +
        0213558603101550321701050532842570497841651484326436846403648475532249) * 10 ^ 70 +
        4941339956871292589957794774179482566759962968366223266271459254601590) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_34 :
    recurrence5Scalar1Second.coeff 34 =
      -((((973318 * 10 ^ 70 +
        5982287048264674442664601413890455942564611324043801315625279751703857) * 10 ^ 70 +
        8178832298617913619314200279330035617721780966700183622515060731871906) * 10 ^ 70 +
        9259985334703646549263495508345202605958045413099116092688636227501605) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_35 :
    recurrence5Scalar1Second.coeff 35 =
      ((((68888207 * 10 ^ 70 +
        9487812614428913793674898161743054938066508430752952526182077128409123) * 10 ^ 70 +
        4719943327355651936165492005869243460340041508606362850655280876093665) * 10 ^ 70 +
        9311541005658013480860153682082404288016831823068347882477610630360388) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_36 :
    recurrence5Scalar1Second.coeff 36 =
      ((((1633696019 * 10 ^ 70 +
        4708586807241243318659084753651893440980089156660473325122191308104909) * 10 ^ 70 +
        1382678900662714114515444353925479092469732217670695921476245201228427) * 10 ^ 70 +
        8360827196878681198004668879132282173661579885996642676122956547935501) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_37 :
    recurrence5Scalar1Second.coeff 37 =
      -((((1692693275596 * 10 ^ 70 +
        0905508676806610881345891063674021418098087721557492008186552861840935) * 10 ^ 70 +
        7364475693942321938653645541032268744438787559297210615968548497763637) * 10 ^ 70 +
        2046787499244065308677449103507535044280292126709911194817984340299897) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_38 :
    recurrence5Scalar1Second.coeff 38 =
      ((((382670932883485 * 10 ^ 70 +
        9360484009867366993683867561606339729665245569162653262005772981662997) * 10 ^ 70 +
        9874469579932799034957598079212015448119382064388181509145497274663629) * 10 ^ 70 +
        3882289567750566513616372443688740264123210183936323237798934082595465) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_39 :
    recurrence5Scalar1Second.coeff 39 =
      -((((62826732875693633 * 10 ^ 70 +
        2133272718034418264955125889671832717019442891582701375830893316502215) * 10 ^ 70 +
        7351416103961755385475836796365550539369250055279818507233129329182607) * 10 ^ 70 +
        0004835415687340796572254415831401833960407170910411132318058298002296) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_40 :
    recurrence5Scalar1Second.coeff 40 =
      ((((8625443199574565564 * 10 ^ 70 +
        5444813160315188097234308897845590764926407826000211659291058901138861) * 10 ^ 70 +
        2669909382245971672510461041937437061594658000613476950901380040785026) * 10 ^ 70 +
        2452149693878307529089541110324613708606475964997182131481656892112336) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_41 :
    recurrence5Scalar1Second.coeff 41 =
      -((((1039725281517804100202 * 10 ^ 70 +
        6267400115959723279958251577871505147315527971649517632545158263713642) * 10 ^ 70 +
        1202424581569060730919778694790765582025727733299673067588283309424256) * 10 ^ 70 +
        4604376741526821312142523767217087341733423006527611325507833575000166) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_42 :
    recurrence5Scalar1Second.coeff 42 =
      ((((112645881242746839235438 * 10 ^ 70 +
        8401639876279160814864333549779334909157814874491106095996065004865035) * 10 ^ 70 +
        2344578396948299619977352212470203585001256179710733340843803315272738) * 10 ^ 70 +
        2576946739753207009038859315858155112215714696002980456968737890708216) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_43 :
    recurrence5Scalar1Second.coeff 43 =
      -((((11117496934321973844322050 * 10 ^ 70 +
        5039580254738072976629352591452751339371745429724591869794693225155827) * 10 ^ 70 +
        5034416734081127522331728550407239787874515208973753547820073750792011) * 10 ^ 70 +
        0660280093974710224350713828602655777863916642293889937488968801538752) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_44 :
    recurrence5Scalar1Second.coeff 44 =
      ((((1008241401117117617402482268 * 10 ^ 70 +
        4673072301720266518345392161110469888626836675268967496400177888718947) * 10 ^ 70 +
        0844074402158481959753941134962959752245120169862267307334685461206583) * 10 ^ 70 +
        0836100711880004262092764607073397202177819829237968557398593338323031) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_45 :
    recurrence5Scalar1Second.coeff 45 =
      -((((84534992751178953747803082408 * 10 ^ 70 +
        7382720236276998181867031727140944887655311738141340858329282159944198) * 10 ^ 70 +
        7924161569825586430641389227565782947917727867777117131266413498819348) * 10 ^ 70 +
        1863970522214414558674126649078516557676689355676836176566786915898564) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_46 :
    recurrence5Scalar1Second.coeff 46 =
      ((((6582668143077573013699332718737 * 10 ^ 70 +
        1959283664260404452220045601267619649336016543764161933968689981089007) * 10 ^ 70 +
        0417623043229884471760100759622319368473760602499340566097389888508819) * 10 ^ 70 +
        3337017804585801276971734695640698807460318765441597661744668443541517) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_47 :
    recurrence5Scalar1Second.coeff 47 =
      -((((477760556272013972296409457139329 * 10 ^ 70 +
        0414761860496027658460364423025112993926780192658655960746233879863432) * 10 ^ 70 +
        4544098605060362850001875132453551585646745312538285690140731183721452) * 10 ^ 70 +
        7235850040788967314606629920242884382551982084874990237892433849985851) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_48 :
    recurrence5Scalar1Second.coeff 48 =
      ((((32412984948609326545105954546910013 * 10 ^ 70 +
        6703146609075143079992594727039023859813987797101876559091002536996385) * 10 ^ 70 +
        3793857748925735370951190115476292671700231386611279219126294942321912) * 10 ^ 70 +
        0211768865374223720226137473410218966671508483083908259346772963204778) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_49 :
    recurrence5Scalar1Second.coeff 49 =
      -((((2060522714127531828742748564350919842 * 10 ^ 70 +
        6146315730799001098212593027814120221972940562963690457091187673862617) * 10 ^ 70 +
        8822501679951763224127910690190139629376459816638072765181856681172183) * 10 ^ 70 +
        2897966673658921744502371675229879829810024093107622226251783081406853) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_50 :
    recurrence5Scalar1Second.coeff 50 =
      ((((122992795541777090415334233740725725787 * 10 ^ 70 +
        0367987750748871789405018449031438135056726163487524092365649790142838) * 10 ^ 70 +
        4745046960379990187967581272102044214740527375551691197478227695517319) * 10 ^ 70 +
        0485435839289642440875873792467787473836674578661698665893092821378642) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_51 :
    recurrence5Scalar1Second.coeff 51 =
      -((((6905582060007374351583500994896631106065 * 10 ^ 70 +
        4084171352702142600723068846757706482385094206807289177481735799365173) * 10 ^ 70 +
        7474152301159918221853179397930062985546854560522755344819998807685509) * 10 ^ 70 +
        5344245625634161343242410808445139081044076276673939252767020710567577) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_52 :
    recurrence5Scalar1Second.coeff 52 =
      ((((365273230635790780542225896173847149570221 * 10 ^ 70 +
        6553595110317134106891170815501759040073123406468885098379595897637030) * 10 ^ 70 +
        6800038531715842050413288958131951924650262867054207143656592741745284) * 10 ^ 70 +
        5830442162596896738087062108669701325199147968858427254026922688370992) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_53 :
    recurrence5Scalar1Second.coeff 53 =
      -((((18227686327095631322824366289910221104532808 * 10 ^ 70 +
        6561227891797815432242773221776125028441750880883512519694482322298733) * 10 ^ 70 +
        6306145386799130030521155018589163396375331204384184229358953319987555) * 10 ^ 70 +
        5617617614888000210967343346452235159735335224534007979125329615923356) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_54 :
    recurrence5Scalar1Second.coeff 54 =
      ((((859157195476453370452047540365929471632541719 * 10 ^ 70 +
        0590576826408370517761600313874406508494759070821210371797585966427063) * 10 ^ 70 +
        6968110005163124983681669584384320617178889204817379418989746842854473) * 10 ^ 70 +
        7043951825911790782457983910854763023269990829370272339230968689917151) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_55 :
    recurrence5Scalar1Second.coeff 55 =
      -((((38292357100454880730195855431921881833909960782 * 10 ^ 70 +
        0261471720380760132410390876285419088470072860606230664163506705482392) * 10 ^ 70 +
        8390614240344249649976708087431858228879078641232442739150527694357083) * 10 ^ 70 +
        3561266251989609054023516319899655479911748962174543597112768998635501) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_56 :
    recurrence5Scalar1Second.coeff 56 =
      ((((1615346120704501433721281208035533148100568038085 * 10 ^ 70 +
        8215187658107481506505500830710232912738637844987630743751879351707429) * 10 ^ 70 +
        6601550809173618498521162897114466397152303733974708956063674156642513) * 10 ^ 70 +
        5514975065513215691555727130812213486209662733962595107930001933498058) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_57 :
    recurrence5Scalar1Second.coeff 57 =
      -((((64549947266150018004941025815216506842009933640127 * 10 ^ 70 +
        5374286299583216016452777561682081730927372613060898606077540452795542) * 10 ^ 70 +
        9371362747402380199442876735478104336262638379968564829831707064760876) * 10 ^ 70 +
        3314617441662113719010044706216862128434092557740581051207479688549707) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_58 :
    recurrence5Scalar1Second.coeff 58 =
      ((((2445193402691476823906755007908047777951355466302124 * 10 ^ 70 +
        9657175483570913287641850676117834631842290040649093240261686860796098) * 10 ^ 70 +
        1832459605540896070800557794654687571326020709944284656982176836447656) * 10 ^ 70 +
        3423810401672093598269373840767112364225753296442869256651661053691001) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_59 :
    recurrence5Scalar1Second.coeff 59 =
      -((((87856367505155538698390828794532102089988661545402752 * 10 ^ 70 +
        2213893051398292758147341193263413252604666301285299309825315677427426) * 10 ^ 70 +
        9453436182250144952529122298499123074583636960758218007871068740198841) * 10 ^ 70 +
        9844257114613753164465917836824606345002211391799305750994797714692535) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_60 :
    recurrence5Scalar1Second.coeff 60 =
      ((((2995522142880418439762695523475926051853011561134006679 * 10 ^ 70 +
        3576836204858571603147117566116304185434423931051988226220870231454492) * 10 ^ 70 +
        4942564534709265952188141949599437105088014927177752926670427022258186) * 10 ^ 70 +
        6095914475277861464856028226301928540524862306813863500578787809167235) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_61 :
    recurrence5Scalar1Second.coeff 61 =
      -((((96948406282166301186290605800911478057786759124355128383 * 10 ^ 70 +
        0726217038888980662511440036234606809209859637288363665527546179258586) * 10 ^ 70 +
        9939168641734071631761062773750299946973131658801739203220192778701171) * 10 ^ 70 +
        2826334718552885195919848348543294525143609733659201218634106018249177) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_62 :
    recurrence5Scalar1Second.coeff 62 =
      ((((2978708370083423234948820746537718058750605847981111147727 * 10 ^ 70 +
        7153023826653735784875541122453477833968628552210894088230781372261161) * 10 ^ 70 +
        7222580757453727023314898227058120549516060396568090851373206787646471) * 10 ^ 70 +
        7063359990177055661592288732520733592304353345197756993796828635903646) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_63 :
    recurrence5Scalar1Second.coeff 63 =
      -((((86873409841170187985720719025928016523315796815828295440564 * 10 ^ 70 +
        1843776292727181062517043546691408637494779095485849695853843611116519) * 10 ^ 70 +
        7554280414981678815487773662567219643204404144527150879849829926708284) * 10 ^ 70 +
        8271828716530894416699451348906439607843815184558568031460544468838714) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_64 :
    recurrence5Scalar1Second.coeff 64 =
      ((((2404050022058209708990185439610551017189444065140893141297133 * 10 ^ 70 +
        9377369668944273476074229896126205485792691003312279089397724670765280) * 10 ^ 70 +
        9672359784802133493660751978846643910325992534708440988411056497895268) * 10 ^ 70 +
        6236331927048073818670727371756840574296941332797374168752657850660604) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_65 :
    recurrence5Scalar1Second.coeff 65 =
      -((((63074566449532530952160026718233901279284903413147865540062470 * 10 ^ 70 +
        2323187743250359639096862579529984804533742581630711734471452447442469) * 10 ^ 70 +
        0483477439645077886965067287741208534210423356414687782367187307816919) * 10 ^ 70 +
        7548432800329110749847277700712426582421914998341690842429244000351349) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_66 :
    recurrence5Scalar1Second.coeff 66 =
      ((((1566884000500467633984959920545776863363628571320934210159592409 * 10 ^ 70 +
        4497552974508624991256071357175472851245188322452953746463777945260344) * 10 ^ 70 +
        8798082189202336893422848039866701882266798744819933410608808489043994) * 10 ^ 70 +
        1584711600329197880848800231869622423159640645893596360729834705396519) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_67 :
    recurrence5Scalar1Second.coeff 67 =
      -((((36775335728505171749263507997348686057143072493653093198587175395 * 10 ^ 70 +
        1181284893435434123838325356313571114453467052569196943145453468463989) * 10 ^ 70 +
        3696717124183466711764135710992143454584520024385225532352267504881390) * 10 ^ 70 +
        3338245578184804103100093575048107743720399756982139342523688923390943) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_68 :
    recurrence5Scalar1Second.coeff 68 =
      ((((812699838276751925481319342759178815756749996122734018678089402203 * 10 ^ 70 +
        6160922655717758169623125862289310985483176259371299416425095083138800) * 10 ^ 70 +
        4314720627024978812019036197421596060606704153854941539155374320848463) * 10 ^ 70 +
        9757481549275826974131776646246200314153364490655449309322487591206256) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_69 :
    recurrence5Scalar1Second.coeff 69 =
      -((((16817452390601855962159017586839780896749320534650026393876367836545 * 10 ^ 70 +
        3815574394686803456836685000367425941494033268081462538844095708404838) * 10 ^ 70 +
        4224539892852336148935962621989259848044476725414746743956003973395821) * 10 ^ 70 +
        2913983368085211431493243568340463766598558688370076136711588019441922) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_70 :
    recurrence5Scalar1Second.coeff 70 =
      ((((322846252424174516614489973323641554344766647570270720587509394850861 * 10 ^ 70 +
        0669404508559228080955405647250108941606738058728316118748863649837610) * 10 ^ 70 +
        4349528328661600445595294714080391681928506590178535580487253822375157) * 10 ^ 70 +
        9029628354515660430722125738368786553007909726104010763836772095316654) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_71 :
    recurrence5Scalar1Second.coeff 71 =
      -((((5652390735577005896094441214622840661051523561274757151852018169630942 * 10 ^ 70 +
        8223171271131656767276331303549790864377092117379928952033014733661218) * 10 ^ 70 +
        1411755290703548548428320038690069059587136223372191644643818489371123) * 10 ^ 70 +
        8796708758164308212917247611882426787982484988076785363332693767420065) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_72 :
    recurrence5Scalar1Second.coeff 72 =
      (((((8 * 10 ^ 70 +
        7100019114250866252647849600224466111195491167689257869099314149919360) * 10 ^ 70 +
        2676670716921407789332355238508418449203377351492627799992821539101487) * 10 ^ 70 +
        3748172277127219742359370488394148350500124636119923442613179869566147) * 10 ^ 70 +
        9767679435656432843212235259822720232408392764030089138234832396206639) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_73 :
    recurrence5Scalar1Second.coeff 73 =
      -(((((107 * 10 ^ 70 +
        4469393259483184121490226686315066754306508795459520639338775553146526) * 10 ^ 70 +
        5806364877416712459628562077504330700436453489376731489210188385528170) * 10 ^ 70 +
        3618542153889601136802594434265851907811707779577884724654295365945292) * 10 ^ 70 +
        2561867061412274242307236211938814001753897189186476592848301470312060) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_74 :
    recurrence5Scalar1Second.coeff 74 =
      (((((662 * 10 ^ 70 +
        2898302433861855835646678368084688512205044810065582054137620955180624) * 10 ^ 70 +
        5110414474248147277217057974610720837670150423606083793256903054661666) * 10 ^ 70 +
        5634570724974646174253458199042328702779223600721920738600808059483475) * 10 ^ 70 +
        8767970782952850628900786671789444228641066909834558134795526534127753) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_75 :
    recurrence5Scalar1Second.coeff 75 =
      (((((16171 * 10 ^ 70 +
        3439166237988271272973813309219477372196749101407593102278273191076689) * 10 ^ 70 +
        9447822670006014320214030995617359940065617427253381750572090971983561) * 10 ^ 70 +
        7939170747993508533317090041899321074184108751068885200690872620490873) * 10 ^ 70 +
        5174373396585558009100662542862949230312738081723471518101223918235343) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_76 :
    recurrence5Scalar1Second.coeff 76 =
      -(((((842170 * 10 ^ 70 +
        9340189010402702324604535733944193999284071957260551658733208213956360) * 10 ^ 70 +
        6284262947323489035939145207674153116038168516130784451718388069304785) * 10 ^ 70 +
        5948143137344392795146135761482975586214798205440153087232023837148569) * 10 ^ 70 +
        7476991747823358101128071647459480401327469360614326900832173992816812) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_77 :
    recurrence5Scalar1Second.coeff 77 =
      (((((24853783 * 10 ^ 70 +
        3362956351105920626523006192289441794446883144001138925645336704891759) * 10 ^ 70 +
        9831809560356866770810072957494551182155776155997357999544770754672841) * 10 ^ 70 +
        0596381826268430277977574365261411000146622253246298022140873529995943) * 10 ^ 70 +
        0152645705080724452689195489395240482326999633686145633806237722591160) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_78 :
    recurrence5Scalar1Second.coeff 78 =
      -(((((599204361 * 10 ^ 70 +
        7246758413462695934343912755469264209491043330977681528307369961504033) * 10 ^ 70 +
        5796785865354598981276737664271611676700818216808590571688044892953741) * 10 ^ 70 +
        3680827065446939979077929023388604227180258277185301559990004216063190) * 10 ^ 70 +
        7341049613994347787605899436605789910255107859063451221963314389317110) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_79 :
    recurrence5Scalar1Second.coeff 79 =
      (((((12836769574 * 10 ^ 70 +
        2764940421519523763018745076992629193716636715967571885651254722775937) * 10 ^ 70 +
        0529016587161950222176663573506674870256548378127933015852154493549664) * 10 ^ 70 +
        7697005419572214271649803018544409672980590320142783950150284481770613) * 10 ^ 70 +
        0113338601351543117156080672163117922203353029625635081441927766884018) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_80 :
    recurrence5Scalar1Second.coeff 80 =
      -(((((252670245491 * 10 ^ 70 +
        7876691850481932479301069598259570001451852728387569581574086174897549) * 10 ^ 70 +
        4623770699471436484223206641317691483367856777296032578712867793323070) * 10 ^ 70 +
        0142620833015964355144024720851137834235631564139137010183253373278832) * 10 ^ 70 +
        1159939595510353341613959519011499668185298157042170242257367558773644) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_81 :
    recurrence5Scalar1Second.coeff 81 =
      (((((4647321293835 * 10 ^ 70 +
        9553094125187698912422750218235392058725579722586579947369921923401506) * 10 ^ 70 +
        4556158217134946320667062017485384437942141039035296489210326942828254) * 10 ^ 70 +
        5952603682582237958665055167091967422168753713973981158268445673932236) * 10 ^ 70 +
        8888842133035995510972092029553035664239291888313770936441584947582410) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_82 :
    recurrence5Scalar1Second.coeff 82 =
      -(((((80662175400187 * 10 ^ 70 +
        9707865986961291314322938506058814997284886106148008204487062793859542) * 10 ^ 70 +
        0914511462734384098790999682402389347677842155552595491655141392567956) * 10 ^ 70 +
        3171349695075353212505180481511936654441439363124033276207763786912073) * 10 ^ 70 +
        5829526147317142484400112057001383353886477183391250623612464318117998) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_83 :
    recurrence5Scalar1Second.coeff 83 =
      (((((1329513031013505 * 10 ^ 70 +
        1513572131366536730768819986999520215981559156530659676755845018732679) * 10 ^ 70 +
        6698240941514363641403748049500794943434512810044177090073531690385409) * 10 ^ 70 +
        7693911179178066759104889107320096043105671800207011305157398662516174) * 10 ^ 70 +
        1122079011644475568594343053255022815397755109456109076008809482515721) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_84 :
    recurrence5Scalar1Second.coeff 84 =
      -(((((20900417025490218 * 10 ^ 70 +
        3988792921740261835577517458725950401049922203796492506396171675353795) * 10 ^ 70 +
        9238662725850322273977328874878518883461259715472752563341930764323142) * 10 ^ 70 +
        1551465828950775024283467713895660817445624995851928385595307508212033) * 10 ^ 70 +
        4491491540569812354853382731752590873113134443268565457612719045751400) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_85 :
    recurrence5Scalar1Second.coeff 85 =
      (((((314360445686035064 * 10 ^ 70 +
        5967550665995390304540907070677587204037119665369657724736661893862315) * 10 ^ 70 +
        1109867043815120212073516653888450460299416329168686732133063446954045) * 10 ^ 70 +
        8309337813620216467258214420742667596669026691344106659988348053965139) * 10 ^ 70 +
        6050119336259818990659449343100686700720854955174026170807987015444391) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_86 :
    recurrence5Scalar1Second.coeff 86 =
      -(((((4534757228861084079 * 10 ^ 70 +
        2342476122112067838101162120796367832832487508941577650705161681548458) * 10 ^ 70 +
        5158762389199901180500115832903346522133401113484574008786131692203628) * 10 ^ 70 +
        4140182792443860112499903735357793613911898071070838457310097049037660) * 10 ^ 70 +
        9663668901833339231826984749248175841202781877406483063819142476513105) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_87 :
    recurrence5Scalar1Second.coeff 87 =
      (((((62857301545997284828 * 10 ^ 70 +
        7224178605962798078728087669239135233914587948237050470677684080936442) * 10 ^ 70 +
        1849762419528121055496821647641154334780573540906085633886283121774842) * 10 ^ 70 +
        5102933343528527389124785239479449517211552091104777650904986311109667) * 10 ^ 70 +
        3060572883798330125876050010027846586330051119135686542097169533212284) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_88 :
    recurrence5Scalar1Second.coeff 88 =
      -(((((838497168744266757114 * 10 ^ 70 +
        5840622926559399326145572515537834740624990363366731605982821911788881) * 10 ^ 70 +
        5148081227254007494527805968256601385006553194852408223899593263365322) * 10 ^ 70 +
        6939628100472860160303100540677862372076545460221214225579379143404015) * 10 ^ 70 +
        9060911684619167052149950337310527507372976865210378390137729030610541) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_89 :
    recurrence5Scalar1Second.coeff 89 =
      (((((10778278819749930153930 * 10 ^ 70 +
        4404693295009783030711641703509940216128221932946311684973826484357149) * 10 ^ 70 +
        5045682982370239577192025932336880471337582467880647780943301517113881) * 10 ^ 70 +
        7555818658092023403888466813464785185945027702359089357485440576852833) * 10 ^ 70 +
        7958923854433544440119831542202696682225667773736637618821852189733541) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_90 :
    recurrence5Scalar1Second.coeff 90 =
      -(((((133651765273734873138709 * 10 ^ 70 +
        7526880996680499779525729896319218242629186347561705277386809254964708) * 10 ^ 70 +
        8998860643403999871050899350849205432920888753702779084656676842426767) * 10 ^ 70 +
        0883357463848122642034566888784818831413422475846765288749765633246695) * 10 ^ 70 +
        5310114898351009611794490957501004092984193249024545483676354563384553) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_91 :
    recurrence5Scalar1Second.coeff 91 =
      (((((1600259654656452255106582 * 10 ^ 70 +
        0072735915241452439752709631918805823227466932346932080618107857453367) * 10 ^ 70 +
        8148781532003671780873608191878353366179692911585276461979732681758495) * 10 ^ 70 +
        8927829565728248406328159273574923455141631159698525597048692347516324) * 10 ^ 70 +
        9314387540099980608404170655142899657418350690622544948057075971059710) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_92 :
    recurrence5Scalar1Second.coeff 92 =
      -(((((18516594279027208420588900 * 10 ^ 70 +
        9507938992506016887160993969723990340406517047860871017983594596650969) * 10 ^ 70 +
        5964214665958925205525695203267408295599092152241680454063552682646894) * 10 ^ 70 +
        3954076005900623285473675442915719097816552364946978954223648630253678) * 10 ^ 70 +
        1803139295997200453092534789427674983826941817784682477756131120390207) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_93 :
    recurrence5Scalar1Second.coeff 93 =
      (((((207210912244810098835274470 * 10 ^ 70 +
        4229853683445149197770418775344897920446813262629375757131114175504650) * 10 ^ 70 +
        6696528706435174165839699669044516047526719222982644051971122516854714) * 10 ^ 70 +
        8039903846149392563184582167968712283615394503090009518931398675062741) * 10 ^ 70 +
        6489428823782497420586126346955819476839408362408369656755678913128200) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_94 :
    recurrence5Scalar1Second.coeff 94 =
      -(((((2244088371611459160323470059 * 10 ^ 70 +
        3275310407473232205586641341832815021139974447689742913615606989149396) * 10 ^ 70 +
        9225602100553122914638084400639733929351412122757124174350079161171837) * 10 ^ 70 +
        1115188447038647993944915819693978078753696460075355923820760517873060) * 10 ^ 70 +
        6525825107430877656035274232367559793888929018098946816163937430724397) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_95 :
    recurrence5Scalar1Second.coeff 95 =
      (((((23534918610619182297794227076 * 10 ^ 70 +
        2819294170639179123678106615342324039662379187122560243210082557996541) * 10 ^ 70 +
        0032332200067920160179294412204825008757885014063788039823210496360266) * 10 ^ 70 +
        4437346699971093453906510304247104399547317345124174436703318059339358) * 10 ^ 70 +
        4657364721562245735635813676613227886660578845026096681084676336605939) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_96 :
    recurrence5Scalar1Second.coeff 96 =
      -(((((239154955188766456757391593732 * 10 ^ 70 +
        3667890519426585219703278354922340872234018771441725590621817013770458) * 10 ^ 70 +
        1209850599532916461384235595429362356482265971828972795413436888761589) * 10 ^ 70 +
        6913324749634801971096626481095742812902296329854299160378618578734528) * 10 ^ 70 +
        5731301820173522740510726684684308784499469516376890653986025446035774) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_97 :
    recurrence5Scalar1Second.coeff 97 =
      (((((2355975680885816126061517654260 * 10 ^ 70 +
        8540905166174275745688947513690828842514793199356566164876273647637400) * 10 ^ 70 +
        0389062000379513869554056551131010966967100766802512728585380465157273) * 10 ^ 70 +
        1872458370967916605803607530152140178635632546696686798139172979985017) * 10 ^ 70 +
        6447591403622738468261240277280790383927565949364550666534624735813279) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_98 :
    recurrence5Scalar1Second.coeff 98 =
      -(((((22511408154012918959635827551701 * 10 ^ 70 +
        3177531350549510654902395522974702976746892855526178695884989674356635) * 10 ^ 70 +
        7529933462675561702289303432454321095834085281200551416613977325333820) * 10 ^ 70 +
        2967153536925352259456556852098517462678403122320870905349283968383547) * 10 ^ 70 +
        6209572895074620021094030225346666383405074852952905785809883601196410) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_99 :
    recurrence5Scalar1Second.coeff 99 =
      (((((208726534191025250362615680752541 * 10 ^ 70 +
        4114834991542739041558445447970767252989480243265647668562370850324635) * 10 ^ 70 +
        3429823415421727053274816594141077908074756688073357788506940773600847) * 10 ^ 70 +
        4777042839736092372364975226496677539604085306112420176111589703633930) * 10 ^ 70 +
        5090718568249857942590731292872904674180643393677839627658923355353617) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_100 :
    recurrence5Scalar1Second.coeff 100 =
      -(((((1878828712103667386553521548932585 * 10 ^ 70 +
        7577235535929559149275039006998179477340094319506883322453338065034880) * 10 ^ 70 +
        3154711954391431151555390465110280289062730225666166162459070438193335) * 10 ^ 70 +
        0777054681754576765495745113623115591931153344042890716674345210937292) * 10 ^ 70 +
        8079205915229406749661149007294254701348223569319650680861426522231169) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_101 :
    recurrence5Scalar1Second.coeff 101 =
      (((((16425276362604835465659837915910587 * 10 ^ 70 +
        0539963531668657441733843342597041314103700315444094100583739385815855) * 10 ^ 70 +
        9209459281180308178079765572410818309730690413301717313913789654503862) * 10 ^ 70 +
        3291517561625691724313041338478698096907636707779688160287968182659888) * 10 ^ 70 +
        0593458376491298330837943526194557374348906437879974576639741650641175) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_102 :
    recurrence5Scalar1Second.coeff 102 =
      -(((((139516888476977578961934925114810593 * 10 ^ 70 +
        0709916399423119106816953436334135326616917304462044495669972689225993) * 10 ^ 70 +
        3491852293036427681714498212035470833469766738087726127174517297873193) * 10 ^ 70 +
        8296977464488341992282929352705034593721008115516863178926913356303544) * 10 ^ 70 +
        7403507828345820949475283488616900820609975352482113432896866727892013) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_103 :
    recurrence5Scalar1Second.coeff 103 =
      (((((1151845490775529308710652926279867416 * 10 ^ 70 +
        6533247152685744832790967942809825945292903052041720407071936653040699) * 10 ^ 70 +
        3323704640918769248289448337744778707223424791859670578996783145511173) * 10 ^ 70 +
        1289580373297950359402510937450757129336225980502949530853387449147567) * 10 ^ 70 +
        5653545674901499027277840907080474462835834961753920106428483790177402) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_104 :
    recurrence5Scalar1Second.coeff 104 =
      -(((((9246399807471016720310292563003536574 * 10 ^ 70 +
        7853587507424579828319182506858730461300480552696325535675462337292476) * 10 ^ 70 +
        8284561941142074558668808534647396672396334228055956591371437710202477) * 10 ^ 70 +
        8664462204716201729842381816562119523446789480414564607396861271730455) * 10 ^ 70 +
        7029010940102840956431770371971884848338944877021178256342094056495357) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_105 :
    recurrence5Scalar1Second.coeff 105 =
      (((((72196029612888128956767311389555600318 * 10 ^ 70 +
        7646493295272248264835725884350943712387194009230455698913310786989733) * 10 ^ 70 +
        1855251538582389439507304127455790932553732433247256990056457488607980) * 10 ^ 70 +
        5695074391455686774528991746095370862390802452011617274347514734868365) * 10 ^ 70 +
        1569696591275118865053360192726363031174786240438106517991747577668518) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_106 :
    recurrence5Scalar1Second.coeff 106 =
      -(((((548480876017050839491193488851271054417 * 10 ^ 70 +
        4868329943620471526379960119017630451489114435550702499607528488491618) * 10 ^ 70 +
        2841266832893895086479494759231902450973530094550416696070972012026352) * 10 ^ 70 +
        6500986441796845163201585344307707254778838869564355566897065083457169) * 10 ^ 70 +
        1831818602976507927956156483955470673945145195339186120135770175307285) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_107 :
    recurrence5Scalar1Second.coeff 107 =
      (((((4055618644241102363938709310222100839622 * 10 ^ 70 +
        0090390030824341929045843880659821508067478591707313408996821541194897) * 10 ^ 70 +
        6103875952554244198366761371829648735412987088255009536844078434193385) * 10 ^ 70 +
        1687610010650944966145781642487791483748303984326177280791387357705442) * 10 ^ 70 +
        0889333386247909659155850968849320835772695617569424692536179425800055) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_108 :
    recurrence5Scalar1Second.coeff 108 =
      -(((((29196789526095627036847521561046701737313 * 10 ^ 70 +
        6117404623553201965347671817636755789448243402633634389654939520318123) * 10 ^ 70 +
        2081555831885340115107812238609255406877472922525741081556794185750765) * 10 ^ 70 +
        6739448924262957330760329944783364022395326176025417018048225764514614) * 10 ^ 70 +
        7291872960082938249685480924480082000594510543609563982722192764045028) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_109 :
    recurrence5Scalar1Second.coeff 109 =
      (((((204703719073304600709511046617356340054193 * 10 ^ 70 +
        5157050858038609904066961092951339955115865116138189492977522286994113) * 10 ^ 70 +
        2077776315629238632168051722035457882251581627414161003632322144086299) * 10 ^ 70 +
        3650005634276529387338220076749180583576335592312359073006787332388971) * 10 ^ 70 +
        9763736621348822208986144033337264226280973086894884385469836936960419) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_110 :
    recurrence5Scalar1Second.coeff 110 =
      -(((((1398153835546688894527735407437351047908387 * 10 ^ 70 +
        2801350926337340341675975504506223280562403629217081768690523034990982) * 10 ^ 70 +
        2858681445215835130380693346266044762293395270467331627706645426940063) * 10 ^ 70 +
        4985880849947986576656501267949573180178143249852393106536041820169235) * 10 ^ 70 +
        0935922913699074894854363872795346358611150876118086714191418258255027) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_111 :
    recurrence5Scalar1Second.coeff 111 =
      (((((9305605960233312685787951856726278205652951 * 10 ^ 70 +
        3503121649202026391177008299967690972372562225748220816281779123471267) * 10 ^ 70 +
        6245616099088816186827902599567491242811919872449471041856227629655295) * 10 ^ 70 +
        2052111439522156943884561522009683126670433907239585187745454798376675) * 10 ^ 70 +
        3506021121145305285235619056898992257386233129954078205014794397281654) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_112 :
    recurrence5Scalar1Second.coeff 112 =
      -(((((60368848610926947817023908068463130345977407 * 10 ^ 70 +
        4955638453137187542581834494419636274470826769468860999609573888946349) * 10 ^ 70 +
        2434564470047940025954447364914550440337631889190832960645899716527764) * 10 ^ 70 +
        9865132443632693168254261494516764286568318633795571600095370791313482) * 10 ^ 70 +
        9180500926032843183487291665669900224394101403430933340733308083406516) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_113 :
    recurrence5Scalar1Second.coeff 113 =
      (((((381833568711326706416706549458470614418187792 * 10 ^ 70 +
        5422431655415694193994160657712656862572883010100598843061834936694275) * 10 ^ 70 +
        7973917178187906041864334349127350940467396878486527830508071465250644) * 10 ^ 70 +
        3010845182239321695456006372557875340532750266586412993484944525646566) * 10 ^ 70 +
        9099181148534953880998467255114487801439645608626591708527447017183105) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_114 :
    recurrence5Scalar1Second.coeff 114 =
      -(((((2355262512497548602833062558645188253570702680 * 10 ^ 70 +
        5456247621220427963289948212108533779616310700169871894941847274734401) * 10 ^ 70 +
        3939243011879133888114042013145010619189017053958863790822052962355691) * 10 ^ 70 +
        6230654124026344396338904741839854293600093908224704352786388975981822) * 10 ^ 70 +
        8577956798150827655534106182415494926073184335822615019465548211294389) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_115 :
    recurrence5Scalar1Second.coeff 115 =
      (((((14171515443702420130832523006851593044567628103 * 10 ^ 70 +
        3305664430027959473733245209307319346782491725746933835697041584997251) * 10 ^ 70 +
        3305757325506899541530050124535059884998131641564534036362249441312568) * 10 ^ 70 +
        8357590250388540152655559485130523344605293209723462448939792561622563) * 10 ^ 70 +
        2433331476305465461388265165918475367189216553996092849580423357783962) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_116 :
    recurrence5Scalar1Second.coeff 116 =
      -(((((83197386868591484332457828194377053983288183562 * 10 ^ 70 +
        3298216976202354694873482000783867881677022234043990804995880290659629) * 10 ^ 70 +
        7432657136675375433748008511489698449251547731523127981561511517718860) * 10 ^ 70 +
        0497801940697240345600239436260179537912056920067624080131771015427066) * 10 ^ 70 +
        2025599977802448855115730697246644590893671389617188519113842104190637) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_117 :
    recurrence5Scalar1Second.coeff 117 =
      (((((476673686659621733370361532957342395710476947560 * 10 ^ 70 +
        1898466039273607838223000740465801894649817654941577211263327547766456) * 10 ^ 70 +
        7383741301425986897957033638943909273452194482425065774349179855513479) * 10 ^ 70 +
        6192943044695037411240107528515720413336707583762968297292387860682912) * 10 ^ 70 +
        0679292038282792574970160995000446358155846445133802514535185914186593) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_118 :
    recurrence5Scalar1Second.coeff 118 =
      -(((((2665935334917802041770622147507279193004251460087 * 10 ^ 70 +
        4102765317668930305509482801217097753604154028685902321770798073805358) * 10 ^ 70 +
        8867944124046194630332586782748843813442580350117778250423920525799781) * 10 ^ 70 +
        2786707707329375827974630833235992390707718990247808963801689879490699) * 10 ^ 70 +
        9069270746332620208094621432030643667174526268627889329195501728891076) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_119 :
    recurrence5Scalar1Second.coeff 119 =
      (((((14557643740609904459757098504247654268308720081387 * 10 ^ 70 +
        8964063732320983302770711003088132297433838352553191416363923155626070) * 10 ^ 70 +
        9561947513813874599086185386135521226416676188714989147048135612243741) * 10 ^ 70 +
        8978382135452734798535172182318469661086939122573368354655121813879618) * 10 ^ 70 +
        3312949580120023895589846629105268968170778697735645208416212502294163) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_120 :
    recurrence5Scalar1Second.coeff 120 =
      -(((((77631697220670114238634135759086094938654346398487 * 10 ^ 70 +
        7359522816166756598368429245027790232228350923747110331831758372397198) * 10 ^ 70 +
        7958256859470671046041378603359131164725447911317386044298126639754223) * 10 ^ 70 +
        6406450167071214628688907571797639440201710624931625654877729068258693) * 10 ^ 70 +
        9077867900968818089097875654744339096897724972066182254267584836300614) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_121 :
    recurrence5Scalar1Second.coeff 121 =
      (((((404375218336359741525847933135003507066033665678963 * 10 ^ 70 +
        5956826342962098448761617208013265549630138289960915331862367751663347) * 10 ^ 70 +
        5351076724121007656292052520936400384360447755587444018435424636271768) * 10 ^ 70 +
        7190683211570021180264436603619815207432827122139264471147099567441346) * 10 ^ 70 +
        3186067079435198918932510756198301990652067998931166354227230287214680) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_122 :
    recurrence5Scalar1Second.coeff 122 =
      -(((((2057860515356840843606709155809246741827410671538470 * 10 ^ 70 +
        8068539140435296153768432746171707992567686464023336379843644494944194) * 10 ^ 70 +
        7623931603910710344235324109469749698376968528274432090937924695279996) * 10 ^ 70 +
        3475152487111402780400826847415217355643085644085384411623140011943420) * 10 ^ 70 +
        3795069338401678854872257718306113494509922441105484986138620551493527) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_123 :
    recurrence5Scalar1Second.coeff 123 =
      (((((10233387389570884234016343215160444169368172327311372 * 10 ^ 70 +
        6657642824609357652533641217081992266596721679257568912932900386332097) * 10 ^ 70 +
        1475761350691814683048730755697946784692094225806652886820557613648802) * 10 ^ 70 +
        4518111608183500870213443759306597474591455723718128046473614568681123) * 10 ^ 70 +
        4955462063434428556340418819166834749708711769484555559832290106457239) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_124 :
    recurrence5Scalar1Second.coeff 124 =
      -(((((49736911590720015332269182079521527474383535317636393 * 10 ^ 70 +
        3571331556807197262938737990932716659980279098195355885974271026780945) * 10 ^ 70 +
        9252270206399914726079652045243686469657049711291914449328205862837233) * 10 ^ 70 +
        5293956009955738574474258390615971525124072282874283894990422858026908) * 10 ^ 70 +
        9685227671241249361702724799208167786067178470925836511802463736325658) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_125 :
    recurrence5Scalar1Second.coeff 125 =
      (((((236306548282176822051868525673520938401296697430326142 * 10 ^ 70 +
        2712242493204191231451341749589697754019494786324655411440394574612116) * 10 ^ 70 +
        9547421588577503061018564401493570145606842831746429157883678326495365) * 10 ^ 70 +
        8852181225157567216944778812433987662324578234342330859162449680018771) * 10 ^ 70 +
        9927271816828075932532137099245525589399500367031710252689312110611360) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_126 :
    recurrence5Scalar1Second.coeff 126 =
      -(((((1097715297524572157972725463316773896979240131486287164 * 10 ^ 70 +
        3998851864679671966737624639973991460266777992904460086062983842440601) * 10 ^ 70 +
        9345170335921860160354497822709449773922653871734453193178936062613554) * 10 ^ 70 +
        0400117777086193142185269428374505961386446711906899403477774071670954) * 10 ^ 70 +
        8186233853608765102872133588890550602008468574418667498645556821165148) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_127 :
    recurrence5Scalar1Second.coeff 127 =
      (((((4986525955843899184605314209710791949057997717335749785 * 10 ^ 70 +
        0335658633978201999489443790904505199029600075372526561374953963530064) * 10 ^ 70 +
        9258479224943121103078093260478498022873980606246527553473568025290147) * 10 ^ 70 +
        2970496143953665859272091321611181955728200188211093827283302024265974) * 10 ^ 70 +
        9166448007876828253400376725799835468773161732272304434185943588811798) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_128 :
    recurrence5Scalar1Second.coeff 128 =
      -(((((22155228015836217720039467247715034751900955538338004813 * 10 ^ 70 +
        5094031877846557488219661748613649407587187706348846101214674708811988) * 10 ^ 70 +
        2297754502903135423466105937204429808956693692427818036173139837212592) * 10 ^ 70 +
        4123264680455755908747848447435340468202135756684143301366381719319022) * 10 ^ 70 +
        6913244542994009197218070487185982002248079172079865107167374150935453) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_129 :
    recurrence5Scalar1Second.coeff 129 =
      (((((96293624643372422950250439691645684628369032268742508913 * 10 ^ 70 +
        8406820061122243993034053542068555418947612334011931317284888555289334) * 10 ^ 70 +
        8213876984706083310601203799103978778803052599511660436451202040703549) * 10 ^ 70 +
        7008052840553631105227931615126689798606388764953265497710087958809198) * 10 ^ 70 +
        9871018811225146558358705900186612270069976519075350629240193415745724) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_130 :
    recurrence5Scalar1Second.coeff 130 =
      -(((((409480760374758944407620556156901873411172302450508283486 * 10 ^ 70 +
        2181880518636574860019429988032109245628535783922473690941239575222405) * 10 ^ 70 +
        4595728242519472671026202790635200436896460019872317498028828767807245) * 10 ^ 70 +
        2789997398428865930690068443078417409116042829542573807496568390769788) * 10 ^ 70 +
        9148391978605030245434563897764605004736100735898761697991367079801803) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_131 :
    recurrence5Scalar1Second.coeff 131 =
      (((((1703937847731835336545969508047931776323279123522866451571 * 10 ^ 70 +
        3873338995752374675236716289682884464708951903170348640553299808273736) * 10 ^ 70 +
        7164367100407385141518849911662568183785889774060993372967226288507124) * 10 ^ 70 +
        6121170388696674309120628913575130134372395344086688188460786312130212) * 10 ^ 70 +
        2405303704429576225806697725440538492456640505871804218351343975851010) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_132 :
    recurrence5Scalar1Second.coeff 132 =
      -(((((6939466710602734100575307030129482623896386479565618958519 * 10 ^ 70 +
        4892614274741800696347713852534946407918857238731064696509621143750218) * 10 ^ 70 +
        2331231899054961504861497685278519356814927790480896613910869532618115) * 10 ^ 70 +
        1514256007760330943113503935794315833557073664265581618690969731533428) * 10 ^ 70 +
        1023000592941154990388696962531564807279421025075618873651009926614202) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_133 :
    recurrence5Scalar1Second.coeff 133 =
      (((((27664103388588223621977873359548528457413715738680232794026 * 10 ^ 70 +
        6681937921208166356782928612151479382389071086357515036994515928966517) * 10 ^ 70 +
        9830557221774320524803576703722151385716478169146177554155399170455409) * 10 ^ 70 +
        1030369111283946200278904360118958162457481434056606462650708757503425) * 10 ^ 70 +
        8249105192968189269211734717020999871215723928038118461295603982626298) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_134 :
    recurrence5Scalar1Second.coeff 134 =
      -(((((107966643272721952327893182258127601468414295292167642679510 * 10 ^ 70 +
        0777959289923444526506726623057183514479333887926532114687441706429926) * 10 ^ 70 +
        4391820425002094226577950893849248778405493207474800470126561570028353) * 10 ^ 70 +
        6642153532346655999647913447839056013873246694407192780833582851956587) * 10 ^ 70 +
        8526431062326919331224098424539735558501764993855248630175301369567460) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_135 :
    recurrence5Scalar1Second.coeff 135 =
      (((((412579620522532714456354749885776800559874807629617049048987 * 10 ^ 70 +
        8768095610868132721265604680869558239760299915859903367616601657287390) * 10 ^ 70 +
        7706959268073226169746151451638359547374187753515482739508751784956474) * 10 ^ 70 +
        7465328047739207338028690704368266156385932884058924995936962265828232) * 10 ^ 70 +
        4086417662557590041928571711695445246880211235459797702845603204335761) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_136 :
    recurrence5Scalar1Second.coeff 136 =
      -(((((1543946219809495409434196046251274669313914453831396424717012 * 10 ^ 70 +
        0428865315618235831547970540658445463190000956795375324221219703577424) * 10 ^ 70 +
        4142322284511656413917712691266139135355008358371507598343020954059820) * 10 ^ 70 +
        9710109079393523390007258708974157880173028365119742959528897467351049) * 10 ^ 70 +
        6467799576580705296734883430349423042160267337091130116170044477745702) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_137 :
    recurrence5Scalar1Second.coeff 137 =
      (((((5658772809674980949101150658516077161227530976337460088350476 * 10 ^ 70 +
        2473773424138030540722476181078532912676045239726767297956924189614727) * 10 ^ 70 +
        6479644620541501877843836649781327140259817650715799027857490788627009) * 10 ^ 70 +
        9638679412171842989743202422392515541769860472436602394381925545336087) * 10 ^ 70 +
        6148186400925049034918536914242545289752788843664320777750333125332366) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_138 :
    recurrence5Scalar1Second.coeff 138 =
      -(((((20315895523613224184700127887329949374349315951623515129058112 * 10 ^ 70 +
        8421152125080303100567160933041877150755094588054848602564565380912829) * 10 ^ 70 +
        2710614779924314248363688530776463861308637415289819471791672076348286) * 10 ^ 70 +
        2367127851390096608909097967207085263411026775400345739283080099243653) * 10 ^ 70 +
        2469002966825225327132454789454456772929992217902792061770086172028426) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_139 :
    recurrence5Scalar1Second.coeff 139 =
      (((((71454525125502641355062410665768844336277249906958986869260049 * 10 ^ 70 +
        8542408394384712354588089251463712724748788923175512707375710579883922) * 10 ^ 70 +
        3762003651945596083231283019071634014607355651217577003599930892884130) * 10 ^ 70 +
        3807233986131223334284506230383914827860441577437519187203351576499298) * 10 ^ 70 +
        0163146761528492906290409241425584406313597900028254219112733492025681) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_140 :
    recurrence5Scalar1Second.coeff 140 =
      -(((((246239958214459132017821712241036909485008379189296006488560318 * 10 ^ 70 +
        5487996923088748146789664270867382911471014055961376449238770936634447) * 10 ^ 70 +
        6281889469882642451587673309619584658271668681682935357684486848163386) * 10 ^ 70 +
        3696092197645523520652604733737385606086486584969011686440778632021728) * 10 ^ 70 +
        5453239639100272797526917151827805281617158404002598542566371725052760) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_141 :
    recurrence5Scalar1Second.coeff 141 =
      (((((831526118085378468691184078765495442390124938646189384010182275 * 10 ^ 70 +
        0386584071256895511952918761493636256961087891607472659175716692891869) * 10 ^ 70 +
        0141411133539272809819636519224162066822787469962758763693098788343957) * 10 ^ 70 +
        6274342378476133395686060943349767241539978943369958335064970570952657) * 10 ^ 70 +
        3420065174858786424015142140628210555707867183753501988605580020762546) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_142 :
    recurrence5Scalar1Second.coeff 142 =
      -(((((2751908575134444682339601073136909799162642456984030395070778409 * 10 ^ 70 +
        8372390004781591307145332765477924485611720001517593341091733913977163) * 10 ^ 70 +
        5772197406489308787657365955968871535748046567676982822498922633210077) * 10 ^ 70 +
        5416603837670332273055789937267629000194704492905216406506252782420904) * 10 ^ 70 +
        5075900788570899757952345999620205545237891271373066159230864391712832) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_143 :
    recurrence5Scalar1Second.coeff 143 =
      (((((8926550524866038716560456299752017964533787186451204612885632663 * 10 ^ 70 +
        9789590241030419449580508522955651449106712678185997131788802362477583) * 10 ^ 70 +
        8730272268115986146589102112014923925677995231343538584715111413729098) * 10 ^ 70 +
        3850609905406980504108804316408767700559737044595241968937141161584656) * 10 ^ 70 +
        1184024471341747274476301206565028240482638606604132534905678105546022) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_144 :
    recurrence5Scalar1Second.coeff 144 =
      -(((((28384052410048162330535058490810509831631787295772378053716869399 * 10 ^ 70 +
        8568609434404308728325790276953286527069256603057824683709234389589294) * 10 ^ 70 +
        2829717576033276054445859880551056093220177493481191782611150770249540) * 10 ^ 70 +
        6412249966600227490688915192426262557812484205726286131258247690968816) * 10 ^ 70 +
        1037660787384743158937893443410299826037603818446749061817692315677713) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_145 :
    recurrence5Scalar1Second.coeff 145 =
      (((((88481898043755551976282902636143372982421590928903568122673218585 * 10 ^ 70 +
        0873241467588655601364982611403810510301589701344200566994894910654797) * 10 ^ 70 +
        2410855927278871829154766603843533510433880021916323354184964962846287) * 10 ^ 70 +
        3946355065135231708259253821939495326765790973379546145323455774850189) * 10 ^ 70 +
        6243750031400689240371602024730589220120132180924580996341439784471397) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_146 :
    recurrence5Scalar1Second.coeff 146 =
      -(((((270439887409654161829512361149629491630297282522084554003495281820 * 10 ^ 70 +
        9214940317277640234338217786858176081736283883310078945003357781309284) * 10 ^ 70 +
        2830246620322374534820085569503386916326953160726809457205236922152708) * 10 ^ 70 +
        0196507278285988751451445707042312184754328820023507150302503922220293) * 10 ^ 70 +
        6029467684268209823645830349352463629888319719985944735789375855668753) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_147 :
    recurrence5Scalar1Second.coeff 147 =
      (((((810530064358201821948681034453226985478800521564972513184327162550 * 10 ^ 70 +
        3310915494155337924344245585199090962029827147201850616172116277765396) * 10 ^ 70 +
        6240951273749616561379957817993836917296524010452412850205258985246328) * 10 ^ 70 +
        7375431450910791519526879176600876057721933363880352329847014645077799) * 10 ^ 70 +
        3171923404798376989975752754267629705846011594101154058019091142214966) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_148 :
    recurrence5Scalar1Second.coeff 148 =
      -(((((2382287540489310314354706455157042618545885597661705981712287752223 * 10 ^ 70 +
        3801016353761444254023572600540378366491731474515015722000978945046263) * 10 ^ 70 +
        6287269740894201255235398626168579250088273550795576780488627328112808) * 10 ^ 70 +
        2950327264492655547624192326135331416344472573473233478069964488514605) * 10 ^ 70 +
        0934449138081622819838384646737861030127696838035797097878186886546582) : ℚ) := by
  unfold recurrence5Scalar1Second
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

theorem recurrence5Scalar1Second_coeff_149 :
    recurrence5Scalar1Second.coeff 149 =
      (((((6867352780841231161700723369090870796832522949112317594011768977487 * 10 ^ 70 +
        9474928163908139063009000921402305345143063190144928489846518394888634) * 10 ^ 70 +
        7873342144875767722653978351542341296933573414973930641149850402502721) * 10 ^ 70 +
        0098094987394385929289140134225251630825418692553677902321132179774808) * 10 ^ 70 +
        5117594259327898718463210344758147576687034160295066894107122306286254) : ℚ) := by
  unfold recurrence5Scalar1Second
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

private theorem recurrence5Scalar1Second_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (150 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_150 :
    recurrence5Scalar1Second.coeff 150 =
      -(((((19417665243762636018055543564519089101879193600536238991245740056174 * 10 ^ 70 +
        7442302189298837757610894596526793135730623138294603290427721659365399) * 10 ^ 70 +
        7266965778823149115935827314451267151274310168455480429661338898794173) * 10 ^ 70 +
        6052948690103794427688519476211681474160188829083682629107185060526712) * 10 ^ 70 +
        9307371878138498197789481415093892344337252799192240964373746981166543) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (151 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_151 :
    recurrence5Scalar1Second.coeff 151 =
      (((((53859013795636335576024339359653833810285013147296706048878027426150 * 10 ^ 70 +
        2125965755058586278390728889989632773711881990248669872856382861174870) * 10 ^ 70 +
        3438774487302296359931697705071609100324126159715978154529868181945312) * 10 ^ 70 +
        7187457045231262921886823930747101902448366488030613672004846391644320) * 10 ^ 70 +
        9878162017452633536956506229635972523884351903338805803218577210549703) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 24 = 22 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (152 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_152 :
    recurrence5Scalar1Second.coeff 152 =
      -(((((146559416987678567776360246143036709430536295872493836690502975548048 * 10 ^ 70 +
        4375583068230949564766414468755316785481378844348353811478503992695249) * 10 ^ 70 +
        2256199465313958197146516392883744889050622742502672633718186392648478) * 10 ^ 70 +
        9588492708723426172542259632242753751177775916199653407456623004120540) * 10 ^ 70 +
        6772283107446228826331469445642776541855263727790925802909697537944990) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 25 = 22 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (153 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_153 :
    recurrence5Scalar1Second.coeff 153 =
      (((((391293100557604587757968071379911072986238864411960521700969389740424 * 10 ^ 70 +
        4221607268831513380464997369945158465694523738812497002081979993050019) * 10 ^ 70 +
        5440816425653504161364432266974643190487558240885409116134423757447937) * 10 ^ 70 +
        8549808909402307525743088506323596123857699296838945808170117304227353) * 10 ^ 70 +
        9225545574650020813808251004830961834024413271552765700876335616984897) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 26 = 22 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (154 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_154 :
    recurrence5Scalar1Second.coeff 154 =
      -(((((1025089938764291630590837136352661086722830500675292007759381761915096 * 10 ^ 70 +
        3777176762758917009710349451247957822909848661596968791752858239149985) * 10 ^ 70 +
        7249904770024962848225362059391100465900545414153742812354125617136937) * 10 ^ 70 +
        6265559463128864391572553404998739110728578246989418733085172327226042) * 10 ^ 70 +
        5874667884041389594786184455757546577492348812009569176608794843648208) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 27 = 22 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (155 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_155 :
    recurrence5Scalar1Second.coeff 155 =
      (((((2635301395118584648338633978234591101153662470205069941854648834583777 * 10 ^ 70 +
        9868233877370561009475061803451034278097876743529759466188945665388075) * 10 ^ 70 +
        6855079361370867817571999384660399289564887658017971181412432677619419) * 10 ^ 70 +
        1408159279490757509965563229203639993848758276483185112163804846965038) * 10 ^ 70 +
        8453068861420438284393109325081886694741126209650414262449557296979799) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 28 = 22 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (156 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_156 :
    recurrence5Scalar1Second.coeff 156 =
      -(((((6648802517642317103250731229954231699965911272097271039290000147921109 * 10 ^ 70 +
        0472948274379746660496272788173532844512865945926232750862818285128164) * 10 ^ 70 +
        1602703195885769155570497042130527530402065242697907585022350614973065) * 10 ^ 70 +
        6783986763693600448225651548120439356760574628789584970000071671311904) * 10 ^ 70 +
        6616858158660745845881283672312110315836006742141807643783443599555358) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 29 = 22 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (157 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_157 :
    recurrence5Scalar1Second.coeff 157 =
      ((((((1 * 10 ^ 70 +
        6464053268984390333644370698950237454106527079241470790112307311861296) * 10 ^ 70 +
        8084550676731783455195189763751723816668159810322995292655602388269953) * 10 ^ 70 +
        0938214109666425913698416706537529783427441701189089387934327340880238) * 10 ^ 70 +
        8997041996857170063280542899965736783888990719477961488808197980975190) * 10 ^ 70 +
        6293760961405350926235009336012916742090021188960024263623174252433282) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 30 = 22 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (158 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_158 :
    recurrence5Scalar1Second.coeff 158 =
      -((((((4 * 10 ^ 70 +
        0017021099747927190032403486443129518404168432979281976946639630007239) * 10 ^ 70 +
        4398619834908788728760596564475305024433997483174831855067873387574719) * 10 ^ 70 +
        0045837912585916815091377240609159395801976271912381077965607980079426) * 10 ^ 70 +
        1803869591225326004871897003085210073870309218275528063088885545727904) * 10 ^ 70 +
        5384582816508201927481925530748557987245733973608532094790668026717482) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 31 = 22 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (159 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_159 :
    recurrence5Scalar1Second.coeff 159 =
      ((((((9 * 10 ^ 70 +
        5477498021159321498423007634164525537228914337738389704315243529451580) * 10 ^ 70 +
        2057928667347074774529308115717997486956029217331601778572273671344594) * 10 ^ 70 +
        1188781528650233599692748565353291460222878190627687957914792282904658) * 10 ^ 70 +
        3361136947071092559667873256998505072706460961828186691015334183442005) * 10 ^ 70 +
        9044968852777097305328402022264267306652969031571872517971651892158249) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 32 = 22 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (160 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_160 :
    recurrence5Scalar1Second.coeff 160 =
      -((((((22 * 10 ^ 70 +
        3634272159776328603411939163696786393146604019135522106099151936625797) * 10 ^ 70 +
        6671706543872449485557667193289830859751275898704298666985679525415041) * 10 ^ 70 +
        8620502066411541285022200871921728952696565241227973446720493863702547) * 10 ^ 70 +
        3668449533542849562811322385971902775114348712542587288111436059345328) * 10 ^ 70 +
        7518477639963080828347110812054301551777933202254319873584875926854840) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 33 = 22 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (161 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_161 :
    recurrence5Scalar1Second.coeff 161 =
      ((((((51 * 10 ^ 70 +
        4267064351110448075740136752387894984530280797974153425966896166631203) * 10 ^ 70 +
        8465045685658894212910928650448494681046360905459878537401709475302474) * 10 ^ 70 +
        7996637693244731014098983956201635172118030860163829619782502161493882) * 10 ^ 70 +
        1331405784238023288107728911965573181541228748120835618886015330171837) * 10 ^ 70 +
        4268943591738989677904015709238913154142996414551336744418731377774878) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 34 = 22 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (162 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_162 :
    recurrence5Scalar1Second.coeff 162 =
      -((((((116 * 10 ^ 70 +
        1136445227796019127655527868753708940688739348793802114739615502493920) * 10 ^ 70 +
        3350823570211539398179271026349372703837421987138503468113126151826381) * 10 ^ 70 +
        7997414337218954114381717217085803319874592569371741831763788484364198) * 10 ^ 70 +
        5055209648945493382971338438384842037532619897715442186454251096613465) * 10 ^ 70 +
        9546861289994786020131077058145019236785576994109942825543184392165196) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 35 = 22 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (163 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_163 :
    recurrence5Scalar1Second.coeff 163 =
      ((((((257 * 10 ^ 70 +
        4259976368143413366230716736445182246048135119493521555717465893451376) * 10 ^ 70 +
        0477501308768846878979082465766170417496946718046111087001728832108733) * 10 ^ 70 +
        7968925061747172789695498842033607770451743016193533604395154817844961) * 10 ^ 70 +
        1219987460047358354716539281133639221467554224182123358964680910795873) * 10 ^ 70 +
        8128974077991567091644361097307626415612608416526562277200553428455043) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 36 = 22 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (164 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_164 :
    recurrence5Scalar1Second.coeff 164 =
      -((((((560 * 10 ^ 70 +
        4357354998603049516521690483976772301440639877533058236607351068319645) * 10 ^ 70 +
        9892105945228384119662287598327554603661458944525955296824031627521138) * 10 ^ 70 +
        3573040963187242347393747110527716086521916418204309331613784868953777) * 10 ^ 70 +
        4356011587184101255959787061680799495722756596504719103061511468506517) * 10 ^ 70 +
        3965585154445060571695732530895970086057565754458127046579567198232198) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 37 = 22 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (165 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_165 :
    recurrence5Scalar1Second.coeff 165 =
      ((((((1198 * 10 ^ 70 +
        2086417737806641803274103974037717438373061452132023319703305328290191) * 10 ^ 70 +
        8179364429645363677470306300703291950069258357658799515208440199124001) * 10 ^ 70 +
        8238641099133419316540274567958994577453328327975822243666370040811438) * 10 ^ 70 +
        0187731068716015693439132392498181391638642024779306068960909708905763) * 10 ^ 70 +
        8837421771129520398547294765438465387855978825522040706205773521209159) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 38 = 22 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (166 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_166 :
    recurrence5Scalar1Second.coeff 166 =
      -((((((2515 * 10 ^ 70 +
        9414789275112626300919139809918196223611145507721338443775549255195792) * 10 ^ 70 +
        3471494566038743626750959736751467254609717801413585342071338379168109) * 10 ^ 70 +
        8649291084701001852108995086770505221903721854253761257070789122715253) * 10 ^ 70 +
        9234936457553183214882375449998635672572241595050369142657023783866124) * 10 ^ 70 +
        6276739682277371570726466591400123652473828841011086587030541558479262) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 39 = 22 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (167 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_167 :
    recurrence5Scalar1Second.coeff 167 =
      ((((((5188 * 10 ^ 70 +
        6891670334105282996069445878080367674475231027637796226450534075784770) * 10 ^ 70 +
        9338894288129084855656854139299531778582768995146456806469608045561022) * 10 ^ 70 +
        5896229921258682904925586777381213906860577179802237785213368366383107) * 10 ^ 70 +
        8579508386899383254253164168015247751636003776467753620488675543322165) * 10 ^ 70 +
        6796780398454225455619903015264454473200294174373070552435873145157397) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 40 = 22 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (168 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_168 :
    recurrence5Scalar1Second.coeff 168 =
      -((((((10510 * 10 ^ 70 +
        6778332815704666160427454261877678425505760828328758442763317037306199) * 10 ^ 70 +
        8980500371562796717155189786971401690793150015803298014562473051361697) * 10 ^ 70 +
        2029120136333041861151606735736022873338951966358337750877505970142178) * 10 ^ 70 +
        6943491120109077292165358491045722997526506198680793783915971116622573) * 10 ^ 70 +
        2500962230774174725968647635033118175567901686164203745438253977242172) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 41 = 22 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (169 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_169 :
    recurrence5Scalar1Second.coeff 169 =
      ((((((20914 * 10 ^ 70 +
        4299346765253884480948854304934161162028036741850283292174074361750483) * 10 ^ 70 +
        8823480636470125187249448068382408860815663023716224952487300740581766) * 10 ^ 70 +
        6423841009069326445962561898343547355911158383015612257226075490373408) * 10 ^ 70 +
        5484185759023118295696117016897006949300205386477965971494951196614747) * 10 ^ 70 +
        9129172809177681822634406058130797881586616274326340974262399076990847) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 42 = 22 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (170 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_170 :
    recurrence5Scalar1Second.coeff 170 =
      -((((((40881 * 10 ^ 70 +
        7287068470861535258157569158807620336104326937999638819294495254861422) * 10 ^ 70 +
        0543232299950225727129555200247447488009073495945141254839502184920904) * 10 ^ 70 +
        6673566048735299772283295152678918753319521944634157529882952861319488) * 10 ^ 70 +
        0124011000677060070462029501253515754876128533222435325402789311183630) * 10 ^ 70 +
        5600379433438759199789261107333945872178526359332423535638850142817852) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 43 = 22 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (171 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_171 :
    recurrence5Scalar1Second.coeff 171 =
      ((((((78506 * 10 ^ 70 +
        4742192522131989928392066224579012325162683691294118579055365979516857) * 10 ^ 70 +
        5866570861082016288270739044867382459935943694511967508809152304159689) * 10 ^ 70 +
        7019667824586050292361249503804938048233901161478033885561805468688599) * 10 ^ 70 +
        7053602676355910698927170418362855745335648620907503692550329600727007) * 10 ^ 70 +
        3032665347496040890647473090732797728752287233544144072864676712563366) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 44 = 22 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (172 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_172 :
    recurrence5Scalar1Second.coeff 172 =
      -((((((148115 * 10 ^ 70 +
        0589389636804208681369868869850327817218787967426340412977711655497030) * 10 ^ 70 +
        0979093969989669738251467326891838377225507892438740587141248721647172) * 10 ^ 70 +
        6462940945752614993397533697991000966376566271570504181159464347411179) * 10 ^ 70 +
        4828580297263368211436454361129925021508593001343710218045663056017119) * 10 ^ 70 +
        9209732925482023266497951912959734623415185920360297752208847578296886) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 45 = 22 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (173 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_173 :
    recurrence5Scalar1Second.coeff 173 =
      ((((((274558 * 10 ^ 70 +
        2212724926919017600000300960543923225916882007002852242548117276867393) * 10 ^ 70 +
        7188541397935302043679667988550350385463742071778683278823910614948206) * 10 ^ 70 +
        5247735156275577212053577209562518670108654680839417668322381060859308) * 10 ^ 70 +
        3847635152743656579397265328551463485212265926654206476980736884030591) * 10 ^ 70 +
        0258901070166645415983216006733381854087106697793656353289050538512765) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 46 = 22 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (174 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_174 :
    recurrence5Scalar1Second.coeff 174 =
      -((((((500074 * 10 ^ 70 +
        4110504716343403533066455689557680194761592377755170422969765160815416) * 10 ^ 70 +
        4156527216676757257656080611937431378691680587135725443819111988861936) * 10 ^ 70 +
        7845785263607682519046304576402770457637000741166010161594504038415745) * 10 ^ 70 +
        2120284259769312700983315553140344733967545398121907360322864009845392) * 10 ^ 70 +
        8054884917239491161843033290091764099096900009360093846519725300400364) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 47 = 22 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (175 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_175 :
    recurrence5Scalar1Second.coeff 175 =
      ((((((894999 * 10 ^ 70 +
        3054830174240891862653215448088834159865078639116252561160167808090554) * 10 ^ 70 +
        8123137158505673144182788694196958068486915171651384233542624067038932) * 10 ^ 70 +
        8382489702285233881793388394992237623703725103975642269431239085529408) * 10 ^ 70 +
        2097634332386588072015632659457205987690544801663620565887050097299947) * 10 ^ 70 +
        9850985257806967993007434826027288429615854461089744505052009652745150) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 48 = 22 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (176 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_176 :
    recurrence5Scalar1Second.coeff 176 =
      -((((((1574059 * 10 ^ 70 +
        3803375506049375062796027268579168766953084852377444738324704432037016) * 10 ^ 70 +
        0132702923940394933413231254218488827420732667612838227451460593103868) * 10 ^ 70 +
        3659039646874991913329173570922788411537618865126593366557776231690293) * 10 ^ 70 +
        4356859463783357906060611210366900749101185364691920148877493971677028) * 10 ^ 70 +
        5270067742908237365835029234143991973839307138374787256051524224082683) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 49 = 22 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (177 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_177 :
    recurrence5Scalar1Second.coeff 177 =
      ((((((2720519 * 10 ^ 70 +
        6752143432336720826997031441793628551076373295572042548013494799521882) * 10 ^ 70 +
        8831551244189016753024279118216781095510080989253327716436440388748218) * 10 ^ 70 +
        1048237999964117164256277982203990751344973445132151034381040057370044) * 10 ^ 70 +
        8947250199014835716668880835487748993800542085615262044568635034116942) * 10 ^ 70 +
        3532359572129133275740873308691484577330118576571251241251196471189112) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 50 = 22 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (178 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_178 :
    recurrence5Scalar1Second.coeff 178 =
      -((((((4621006 * 10 ^ 70 +
        0122207201707637997944059417552263490643920762867795532815389371660367) * 10 ^ 70 +
        6314543724220327276136491366988905493864540376594905449371813250592022) * 10 ^ 70 +
        1854077380080378697887955857971359494252724480121774936821803725798170) * 10 ^ 70 +
        1547871605416707719117024560300348584276335223170471728774127311673522) * 10 ^ 70 +
        5114357477382595340014385370616800505657561217523609147296358678090923) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (179 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_179 :
    recurrence5Scalar1Second.coeff 179 =
      ((((((7714294 * 10 ^ 70 +
        8829606267969070410182663017785732891894145702156328719031530274223819) * 10 ^ 70 +
        6615448658348700839520680627848498386556303997361552173331213266316022) * 10 ^ 70 +
        7280300976155232736014518924594681958797045996497466233641307892025996) * 10 ^ 70 +
        0291354029832884024888042942620875056552268735294707667012469212312153) * 10 ^ 70 +
        8479113196624061223479320084326946136970168446256458828714366267369090) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 52 = 22 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (180 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_180 :
    recurrence5Scalar1Second.coeff 180 =
      -((((((12657610 * 10 ^ 70 +
        1597215340963871053767832271478989736506192034330568300283788538000890) * 10 ^ 70 +
        0113662916075506675718143445663074274094830976755373872850636441317623) * 10 ^ 70 +
        6068589716388669148311299559421728011199961707503715797929589920951944) * 10 ^ 70 +
        7296322107446509754816478858617518953923764298241224635364235743051981) * 10 ^ 70 +
        1211537157192427840196149711656161200875108154714726903860037474730427) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 53 = 22 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (181 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_181 :
    recurrence5Scalar1Second.coeff 181 =
      ((((((20413775 * 10 ^ 70 +
        3629657918118206059677661751912667139439365842420157668503694195579930) * 10 ^ 70 +
        2456318598275753347849184415553626226202325550314523283939605206791308) * 10 ^ 70 +
        0797545198514837482273396601068259107727601959107006952779903733530395) * 10 ^ 70 +
        3556050535984638635541059343909776323507665097968137376949264516864781) * 10 ^ 70 +
        1685014387572561627100940789137105232171429260740123300884614182874965) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 54 = 22 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (182 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_182 :
    recurrence5Scalar1Second.coeff 182 =
      -((((((32361681 * 10 ^ 70 +
        7771281914181682156757676661820951480496134325511895239606709968028885) * 10 ^ 70 +
        8997595951571117812870515691584905402576065720182757326928119512049068) * 10 ^ 70 +
        7449743018400676764279441436391038327411801885711673755028580524473855) * 10 ^ 70 +
        3554559549405684348290223873897066222791021966162612640242382601703774) * 10 ^ 70 +
        3114782900014822446563157888705652487829130782397631979311411679764895) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 55 = 22 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (183 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_183 :
    recurrence5Scalar1Second.coeff 183 =
      ((((((50430657 * 10 ^ 70 +
        7344355521333620186703938664371530049138843791330285056075053553313349) * 10 ^ 70 +
        7475383965377637752201935259569419243364114799406576835215650574228289) * 10 ^ 70 +
        5920332057262454250669211687658176333953636634483320750561876512959899) * 10 ^ 70 +
        2731974293452378374328935868005194087821024809349632912001377817576825) * 10 ^ 70 +
        5156545876062157126868795291901010044437901199292545469805366336076931) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 56 = 22 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (184 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_184 :
    recurrence5Scalar1Second.coeff 184 =
      -((((((77256196 * 10 ^ 70 +
        4731705818852595556339577898543832312595535754372701026601706379757473) * 10 ^ 70 +
        6107880724131955400722756922652925339506482048390939509155315997150940) * 10 ^ 70 +
        7144546506560687044474864465640153303712621145791699947750007161768394) * 10 ^ 70 +
        7352654394935093806428201750687491234765104429847893714051674678597792) * 10 ^ 70 +
        3142726912567427276773482689632571205449242872332999335678822196992803) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 57 = 22 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (185 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_185 :
    recurrence5Scalar1Second.coeff 185 =
      ((((((116349949 * 10 ^ 70 +
        2313139217134265493821413397841262643158385619793853536957780724482638) * 10 ^ 70 +
        7102600608207502845995332967702935509029540330191964983170546433962394) * 10 ^ 70 +
        7267292496821471447160538953508711490625631927116120070369790546503761) * 10 ^ 70 +
        3676730724975497566427761870144142400383400275534393627267032581110195) * 10 ^ 70 +
        9484137685400167197713312683605794318771340184346035253485686429359213) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 58 = 22 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (186 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_186 :
    recurrence5Scalar1Second.coeff 186 =
      -((((((172270938 * 10 ^ 70 +
        9014178894400205987373294241980012613243129119609888613069975383861621) * 10 ^ 70 +
        5383607794944171987575266723080830248032152297100870870567076445962454) * 10 ^ 70 +
        7810934936513986776483900139215711073660425060985766281341924842974865) * 10 ^ 70 +
        1417478399671258145481669956326343249730490427071940937845315586812949) * 10 ^ 70 +
        4623520092799029682294493900549631314339343517821706724950672091732121) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 59 = 22 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (187 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_187 :
    recurrence5Scalar1Second.coeff 187 =
      ((((((250777916 * 10 ^ 70 +
        0262672372995632736865411624836820035834683715955087504595059172829946) * 10 ^ 70 +
        4525021875604853503153318886486560869903107860498348826161008303465307) * 10 ^ 70 +
        8299616509903939369941996096687888189273513782145229048360847719024214) * 10 ^ 70 +
        5226188723294197654998252156416730128734737770673078205725922768465793) * 10 ^ 70 +
        6851164763385417582308299478579696002235332646645887567569930475504409) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 60 = 22 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (188 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_188 :
    recurrence5Scalar1Second.coeff 188 =
      -((((((358935367 * 10 ^ 70 +
        5346147433004899243283601999465928320092702648213442349262163688479423) * 10 ^ 70 +
        1278274839998166777754591627642996451890805579665001100274603822067885) * 10 ^ 70 +
        9009867435654725214381755513028436039952841149051312035885023100070884) * 10 ^ 70 +
        4404599151324009541432657681419663249563619854849598145358923186957416) * 10 ^ 70 +
        8428973293289521944826665425608406183685434909729188360558694646184996) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 61 = 22 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (189 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_189 :
    recurrence5Scalar1Second.coeff 189 =
      ((((((505139034 * 10 ^ 70 +
        6302580416013657989087065695369456148727678993555745911001181083000685) * 10 ^ 70 +
        2568874012890054749937543242339609726691519021890646078903499308082855) * 10 ^ 70 +
        9810378983785316099832184148397784060909693279336264658458270115861747) * 10 ^ 70 +
        1747372576740291780088962667497312629757186869273983009054765778526893) * 10 ^ 70 +
        2581612062013548896311630804312963888071695738807421399614012779185425) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 62 = 22 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (190 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_190 :
    recurrence5Scalar1Second.coeff 190 =
      -((((((699022431 * 10 ^ 70 +
        0987260879640469063637846253264686093400170246070760640625832998105353) * 10 ^ 70 +
        4249824788933315659722798811899511321925560569073699885178325430180198) * 10 ^ 70 +
        1742616332458243657438651676337730643255292222926546272006751273396161) * 10 ^ 70 +
        8183514307222054720781129345457638224446629010928767408354874097505158) * 10 ^ 70 +
        0337592242406854519629453161881001118474168459366887859525164896383404) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 63 = 22 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (191 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_191 :
    recurrence5Scalar1Second.coeff 191 =
      ((((((951205560 * 10 ^ 70 +
        7541206312797996041498981051044196393890646435623301497645692958707130) * 10 ^ 70 +
        2233528674097411274886282872160583414881560717643712227679650183932161) * 10 ^ 70 +
        0636285362789130396805175236339936370418069855228572801277541013200700) * 10 ^ 70 +
        7932116050806991290390052566383840695440213840110967794251600710817256) * 10 ^ 70 +
        6831091776889194934093283443700148741704522279464847380581494129763234) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 64 = 22 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (192 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_192 :
    recurrence5Scalar1Second.coeff 192 =
      -((((((1272852581 * 10 ^ 70 +
        6626258321887277625569999671954094927150744711149633864753747759507578) * 10 ^ 70 +
        2634917831870069005762236520705846971585911369299584339095807583425319) * 10 ^ 70 +
        0648486203659837629402452185871637280674732521880438666931972261755669) * 10 ^ 70 +
        7133141869879103032886933440174328416472918714871477721136327047773291) * 10 ^ 70 +
        1999279906110490289976407531681193727986375629680115059070548455382164) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 65 = 22 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (193 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_193 :
    recurrence5Scalar1Second.coeff 193 =
      ((((((1675017931 * 10 ^ 70 +
        2106597968128458642567806943708495606267168287425361943858128458132687) * 10 ^ 70 +
        5156474105790329343376894758067224393745704583152477045219259828628049) * 10 ^ 70 +
        2658758971795133366135922591450661263024299917978679645649271165552687) * 10 ^ 70 +
        3011749398897963003326543589345080948129556259975727021251304950108295) * 10 ^ 70 +
        4802154328202682156403712032124591068457425217291100495025086627869637) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 66 = 22 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (194 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_194 :
    recurrence5Scalar1Second.coeff 194 =
      -((((((2167780952 * 10 ^ 70 +
        3965019337489199296812375649612852578675342054849081070316258629488399) * 10 ^ 70 +
        1176582739236895722169089828734588778665699968078319396845357012267804) * 10 ^ 70 +
        8593968253654921892850990455928870051273175297106711090414688400814685) * 10 ^ 70 +
        0028638886746392679291182908501613289454256288997637463320292453159592) * 10 ^ 70 +
        7637387140604529056024051003800422041187121058606738841260863686576238) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 67 = 22 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (195 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_195 :
    recurrence5Scalar1Second.coeff 195 =
      ((((((2759196635 * 10 ^ 70 +
        7674553577637052015785772586170406393962507587463649162517627949498862) * 10 ^ 70 +
        9682059974095233854514191514179887643283668484827063870456109019581179) * 10 ^ 70 +
        0927799563086934641854035004597837669683998847370560459416967441122822) * 10 ^ 70 +
        5389552041047480814764268580407362374935564361679822699421674892182919) * 10 ^ 70 +
        4353763971049853562355883695677771595269774915590557705128331450123756) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 68 = 22 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (196 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_196 :
    recurrence5Scalar1Second.coeff 196 =
      -((((((3454122454 * 10 ^ 70 +
        9926333279859870334493111876451753721285330695555375467979087654914110) * 10 ^ 70 +
        6745514609511641860813894994410829604136670158693083084638376259920523) * 10 ^ 70 +
        9997613677270605992881241510498890057726932816278415337345761901047335) * 10 ^ 70 +
        0437976421672618013981063629256441231532249781242026440502940694271628) * 10 ^ 70 +
        3348924083666572034060586449772663916047583498616715704337382100612023) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 69 = 22 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (197 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_197 :
    recurrence5Scalar1Second.coeff 197 =
      ((((((4253014574 * 10 ^ 70 +
        8872476536458978021268506146556030972792953226707442091378824443617201) * 10 ^ 70 +
        7534459017756551652734384863227110783244198907748449303654464585560158) * 10 ^ 70 +
        9302728469914764031190903754165429043864208290327727790291146766019709) * 10 ^ 70 +
        6564661473646755601641705267946286758651854679234279926800500566284656) * 10 ^ 70 +
        3110784311988004536788370854283539501435448264784291796520914104568445) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 70 = 22 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (198 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_198 :
    recurrence5Scalar1Second.coeff 198 =
      -((((((5150815787 * 10 ^ 70 +
        7969739458268007241430961267038168728699302763725658489159530683763631) * 10 ^ 70 +
        2065536413562051778182575083637330935529528424240166667738387820693119) * 10 ^ 70 +
        0422489967082611935832882516856834761189214157633531772533281370736321) * 10 ^ 70 +
        1107895340434932237660955525845440739202980927174828931615150142298321) * 10 ^ 70 +
        4937414104717465139542083646050490810410353569396603297070049465114654) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 71 = 22 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (199 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_199 :
    recurrence5Scalar1Second.coeff 199 =
      ((((((6136076569 * 10 ^ 70 +
        6065229664635852798537659984870909044104997231632457782635534547106894) * 10 ^ 70 +
        5696504579597221052596993913802993994751183774355081689318385875175543) * 10 ^ 70 +
        3933041661502479466564337175002109450701501669875025035916520154673431) * 10 ^ 70 +
        3598106405108966022633438272880729313337660160688781947520632605323519) * 10 ^ 70 +
        8013071268557188055561148214763684147760020118862563430133037428007175) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 72 = 22 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (200 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_200 :
    recurrence5Scalar1Second.coeff 200 =
      -((((((7190454133 * 10 ^ 70 +
        8955957101823411395958408409484626824690796152157170671178324924383656) * 10 ^ 70 +
        8564256907376361929808222398812278340444852670548714636669942890121512) * 10 ^ 70 +
        5853180200778889871208842224190936984316807400597392580033741827426500) * 10 ^ 70 +
        7869909370074054229467629801092608458895403053002376362230710523195372) * 10 ^ 70 +
        8001964728568233789345900414090854100426786874729932310118977953977667) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 73 = 22 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (201 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_201 :
    recurrence5Scalar1Second.coeff 201 =
      ((((((8288718251 * 10 ^ 70 +
        4210575528611478727969495932033309813997182631388426822075997037605473) * 10 ^ 70 +
        1822280538316153300044910375974143114019253198368687250455240860774448) * 10 ^ 70 +
        0160742911962823412803316521865821079289623966561845540268350929765748) * 10 ^ 70 +
        0532892854023661341599918723626468824701197614513052629486659917116809) * 10 ^ 70 +
        1771327906834884191857950826925982599160161009893213591786832875540750) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 74 = 22 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (202 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_202 :
    recurrence5Scalar1Second.coeff 202 =
      -((((((9399355397 * 10 ^ 70 +
        8866468037582371900702655144814471877944771316875633750956529967406741) * 10 ^ 70 +
        9606475332691959401625965498489120070797059892954205196178774768239011) * 10 ^ 70 +
        2044769161678262211221653696685938158272622187785741770247096756503701) * 10 ^ 70 +
        7945401649817768473397257911629117457753778948594272306053704489010812) * 10 ^ 70 +
        4361562840686947540814793081286364563525243707531172352357333646984150) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 75 = 22 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (203 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_203 :
    recurrence5Scalar1Second.coeff 203 =
      ((((((10485806356 * 10 ^ 70 +
        2683536908579647180044344518294601676239241478780736423322024372469001) * 10 ^ 70 +
        7212823639374862189503675587998634417182463204409235407357228450305160) * 10 ^ 70 +
        2038307518063899406010261901557669468824353043551494197277955009045473) * 10 ^ 70 +
        4416690049576274070722583821004095888120570600335268771285152027606682) * 10 ^ 70 +
        9770567142598358169648327114210804699258071126255738902776377224550120) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 76 = 22 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (204 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_204 :
    recurrence5Scalar1Second.coeff 204 =
      -((((((11508302204 * 10 ^ 70 +
        1217793123507927173819101616921267357145894433760178252037256260291345) * 10 ^ 70 +
        2246876623779873858272415878048773829622397665524054491465491645824364) * 10 ^ 70 +
        1092025409098408874440528217769089618362290794318094578815941950165427) * 10 ^ 70 +
        7915621779722854214991748405417300715441134375914505079814662262835782) * 10 ^ 70 +
        2865132264597803030293916936456587208164476250240193025636289419022488) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 77 = 22 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (205 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_205 :
    recurrence5Scalar1Second.coeff 205 =
      ((((((12426188312 * 10 ^ 70 +
        4243500627796890966848687071217166901357229635697706399933059094912147) * 10 ^ 70 +
        4655211379590297089764236655685340446926525473559419847802531924170735) * 10 ^ 70 +
        9132163300133614613337093012746703786935251600114592328816566337612295) * 10 ^ 70 +
        6170911221344871462416356976187846470981809251460560563345587701853870) * 10 ^ 70 +
        2522014512326633888238740913234398449081870999973430243278878428297164) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 78 = 22 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (206 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_206 :
    recurrence5Scalar1Second.coeff 206 =
      -((((((13200556256 * 10 ^ 70 +
        5199368559013251627380272476911825001668433542189966631714988515881536) * 10 ^ 70 +
        5085753390186191569889304356631958782910897137130623101677273290946369) * 10 ^ 70 +
        8725382394082240089482122566753322459431476615351229520327310745375430) * 10 ^ 70 +
        4001182956948717799419275809160879774915812459191677625404936221555626) * 10 ^ 70 +
        5583099099507913497492762133438306293044624564644678688650826017035961) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 79 = 22 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (207 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_207 :
    recurrence5Scalar1Second.coeff 207 =
      ((((((13796950411 * 10 ^ 70 +
        0366590464137231880740045642121228533015344044211239183105432502776632) * 10 ^ 70 +
        5236405121057416715897736414466821828567332692738950347935809488636142) * 10 ^ 70 +
        9266704338906366435935959843922712467096401310070738514337890606443404) * 10 ^ 70 +
        9034919014501633168802106626387703649421085704318258947518037024308563) * 10 ^ 70 +
        9459624492647152388527510274930880602307681137305371535983800258157675) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 80 = 22 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (208 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_208 :
    recurrence5Scalar1Second.coeff 208 =
      -((((((14187888860 * 10 ^ 70 +
        9549464195161674791611251377756498733842249763536141473759629268788958) * 10 ^ 70 +
        1281878017359871575655243149137874504385049013911031542661589910696311) * 10 ^ 70 +
        1298814338645713891474232059277278436456912654850210561755361186833744) * 10 ^ 70 +
        3932052510445295792391268224730855517814110098844414519970247963753456) * 10 ^ 70 +
        9931796858776781513229144549386979035731041363631976237021385161679331) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 81 = 22 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (209 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_209 :
    recurrence5Scalar1Second.coeff 209 =
      ((((((14354943044 * 10 ^ 70 +
        5249799842148248546533384448113196677023346059368381044038934355899301) * 10 ^ 70 +
        0335771465127370332591222921434014636906114835652843398968650580998565) * 10 ^ 70 +
        8187205311345920239853257386308788728491473484421786756061072907515356) * 10 ^ 70 +
        7715408840327182328467459718607723458637389261594284992573858276798997) * 10 ^ 70 +
        1132017919254937686296931450115959788334961594191310603771469771813474) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 82 = 22 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (210 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_210 :
    recurrence5Scalar1Second.coeff 210 =
      -((((((14290158426 * 10 ^ 70 +
        0290075667084471378362484605313533027858837619111057743677328060843334) * 10 ^ 70 +
        0904790888412970763942943670807746272635511120197084634260351267409822) * 10 ^ 70 +
        5349689796413821898615909572900103115546894342381958332296078942055803) * 10 ^ 70 +
        0685462858031894713214847471504609887264637375205458124563408746918406) * 10 ^ 70 +
        4548215258017418202852297583346035745921796811887192985906322425874529) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 83 = 22 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (211 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_211 :
    recurrence5Scalar1Second.coeff 211 =
      ((((((13996665429 * 10 ^ 70 +
        4181146938442764495730011668928646426241439665201716301442460449982536) * 10 ^ 70 +
        5169431341358579902024329752406502187537340513206780574240401025985704) * 10 ^ 70 +
        2173264561579851831423158110302990537482547493407946981256680427488674) * 10 ^ 70 +
        6143646544474255346732583186333781943607109068962879336097979487790894) * 10 ^ 70 +
        4664939782623779205084341124794805646659464347905513960551348385379820) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 84 = 22 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (212 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_212 :
    recurrence5Scalar1Second.coeff 212 =
      -((((((13488417085 * 10 ^ 70 +
        4158993751145902676864202299367220198000859346836494025577501465392756) * 10 ^ 70 +
        8161491363176882351128681893489997632810979466059219093485494125661827) * 10 ^ 70 +
        0957668138674708348479296890918182184433828402470504012873038798727498) * 10 ^ 70 +
        9691771669817912426723630511345562216881744552100413813815195870488095) * 10 ^ 70 +
        2339075855173431115051151435018803023135518488296700368550825752058633) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 85 = 22 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (213 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_213 :
    recurrence5Scalar1Second.coeff 213 =
      ((((((12789085290 * 10 ^ 70 +
        1722798559786225834398837307050523337433687970634508903309476091138586) * 10 ^ 70 +
        5665981906086460184475063606166240166156333103292717493518158203202412) * 10 ^ 70 +
        6752745614846679558015267344750180108200024555736271050940445521138161) * 10 ^ 70 +
        3552926734927249525571105845273802918297830825992921436610750573625223) * 10 ^ 70 +
        3821342338033664473348684152922805258870154727728395258417835049089894) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 86 = 22 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (214 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_214 :
    recurrence5Scalar1Second.coeff 214 =
      -((((((11930237918 * 10 ^ 70 +
        7128769150990495432908819468053425997594162678221988110683851174115682) * 10 ^ 70 +
        4544523282875018708398274950868888564253207100439300797090181983932864) * 10 ^ 70 +
        0116792058419266492938564996482774841311961530759028481910458584859511) * 10 ^ 70 +
        6516409460665741538174597438684121252879720264013570355927543781146305) * 10 ^ 70 +
        7342671508031364444626495089761972800524957530429457563788633724163858) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 87 = 22 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (215 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_215 :
    recurrence5Scalar1Second.coeff 215 =
      ((((((10948991961 * 10 ^ 70 +
        0412405055049348289747342008891416241959285150837345859678593300162180) * 10 ^ 70 +
        1773868880830149889512432340569437733276076008190982641243241647416459) * 10 ^ 70 +
        9588965670344115244411575476749078431019259830665186356508275396552795) * 10 ^ 70 +
        8400842906306960394721411004767086486219809951602751630614213070823774) * 10 ^ 70 +
        3976415153121954192822194358080247466251699800210159735544899721405719) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 88 = 22 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (216 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_216 :
    recurrence5Scalar1Second.coeff 216 =
      -((((((9885384067 * 10 ^ 70 +
        9312472246342347241697777575899836782602954946361369316633570546588622) * 10 ^ 70 +
        3522244046649002007167485289424477988455972667165451261875269242039435) * 10 ^ 70 +
        5905745775247701544536943983041666897455750093057293059135355205213029) * 10 ^ 70 +
        7058608420715553595794906025386383576165929620089892219851382657409846) * 10 ^ 70 +
        5966388854236333488535787137967767027550333074450113100533869626555829) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 89 = 22 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (217 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_217 :
    recurrence5Scalar1Second.coeff 217 =
      ((((((8779714564 * 10 ^ 70 +
        4874295274577421950963049727981689948207584916595127500960389939815192) * 10 ^ 70 +
        7649613956009068605364419978628240689902971282416329894921991856631970) * 10 ^ 70 +
        6915811152322021021003411625790756302320994917625730306615122690260682) * 10 ^ 70 +
        1966866108447194225609252016060964514600752178097863294101473433051983) * 10 ^ 70 +
        0460395278041785671093703124123967969860109734323672619833156647829086) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 90 = 22 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (218 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_218 :
    recurrence5Scalar1Second.coeff 218 =
      -((((((7670104250 * 10 ^ 70 +
        0419919108819855682710751976642944169892534740099349908196088497322893) * 10 ^ 70 +
        8517269065957334066008009200229814179909815791018729210118755564889311) * 10 ^ 70 +
        0752526370107596120894472902274886351882121986581557047432874153692293) * 10 ^ 70 +
        8073029538063777979665849113456723298650258065288106193549100905189293) * 10 ^ 70 +
        9326380037939195824791704131210578221895954240321166959202640789933690) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 91 = 22 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (219 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_219 :
    recurrence5Scalar1Second.coeff 219 =
      ((((((6590459890 * 10 ^ 70 +
        9229525048990422415037377679160527350959136425589014426844065490101567) * 10 ^ 70 +
        1428661024159600200437817045106397089541261309209130613914339157055101) * 10 ^ 70 +
        0406400781939056080460149602843259331833696645395618156490424421300681) * 10 ^ 70 +
        9737081722823208017265515483752186322330687698537987568116876180746163) * 10 ^ 70 +
        4112354699184839761870629430713882446969345270663908373433576258088967) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 92 = 22 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (220 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_220 :
    recurrence5Scalar1Second.coeff 220 =
      -((((((5568982412 * 10 ^ 70 +
        1642480120952573075496535594802740189057580888394381982562866169139273) * 10 ^ 70 +
        6147033988638260956525520251858685676327778799834177585923673702664673) * 10 ^ 70 +
        6432493340358594829578727317542551160637707363291928453704243372350531) * 10 ^ 70 +
        1092924199065610407137866918974753455383136226319093521514865061739127) * 10 ^ 70 +
        8407764920952649094902455040149237952650127111445065463449785434961872) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 93 = 22 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
