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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
