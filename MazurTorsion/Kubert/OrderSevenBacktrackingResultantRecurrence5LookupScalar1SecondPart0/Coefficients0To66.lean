/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1SecondPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Second coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
