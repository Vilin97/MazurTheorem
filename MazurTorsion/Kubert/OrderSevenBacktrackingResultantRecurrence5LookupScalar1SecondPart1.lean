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

private theorem recurrence5Scalar1Second_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (221 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_221 :
    recurrence5Scalar1Second.coeff 221 =
      ((((((4627281395 * 10 ^ 70 +
        4723996219364626995676320700991662822230715675149901164230467614130796) * 10 ^ 70 +
        0280924520358667790592523132416289928456006876418517386855508480513446) * 10 ^ 70 +
        1323650855270747611222773069785741588300583504403408889125989909044814) * 10 ^ 70 +
        8323879599044358650360775865786764161628689417538156211201918159784071) * 10 ^ 70 +
        5989112637703649489351448645658714889713220765195851789903955946451385) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 94 = 22 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (222 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_222 :
    recurrence5Scalar1Second.coeff 222 =
      -((((((3780090621 * 10 ^ 70 +
        4076661579460552379332291802481365452437562902866042281399029946711940) * 10 ^ 70 +
        4736091619301323575730711456653088556531988583325155057380987472808335) * 10 ^ 70 +
        3171051181920079358976507296838863701203356996092574844636033849580672) * 10 ^ 70 +
        0761752293602274645441160684031928849539702625552547191090370406321701) * 10 ^ 70 +
        7563361583688297085796616088932104009140448767492063092557355161401051) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 0 +
    223 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 22 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (223 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_223 :
    recurrence5Scalar1Second.coeff 223 =
      ((((((3035520563 * 10 ^ 70 +
        2130427222058795569991731004099159774966143134153440003168994099747866) * 10 ^ 70 +
        1286242623041834096270128263099663381434433678628127678882513887334314) * 10 ^ 70 +
        7301443907631646697849106695501768542383672433275820028119392389099277) * 10 ^ 70 +
        9155485940676843610000562532624844165896011879081494363556746493495693) * 10 ^ 70 +
        9124475682959874603851006434778679068430592571885820119368267126235555) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 224 = 0 +
    224 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 22 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (224 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_224 :
    recurrence5Scalar1Second.coeff 224 =
      -((((((2395740850 * 10 ^ 70 +
        6079990844641181488436871209874580370694353555709605634045247202600441) * 10 ^ 70 +
        0746007386627683873550883411721108124457470197456458536578579507898181) * 10 ^ 70 +
        1104973521030855459500596024876555165245647739778993598393326466817809) * 10 ^ 70 +
        6601934198875739011017757928744538533809715549869170041428796990789621) * 10 ^ 70 +
        0321757778697897028098762921716516429663085086016660262770215633087653) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 225 = 0 +
    225 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 22 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (225 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_225 :
    recurrence5Scalar1Second.coeff 225 =
      ((((((1857961575 * 10 ^ 70 +
        1919623111778771604390104146127881955560946123121154554024310056180140) * 10 ^ 70 +
        5615175672777269499176232735272763463349749943453694748318291122597174) * 10 ^ 70 +
        1848527160724504890121436287483013257220485489536267692662268933471735) * 10 ^ 70 +
        1027480008693710761067184267147868527869467041118788299454531063065508) * 10 ^ 70 +
        8091811138041782969024072707561043085961929923259156817526082139944309) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 226 = 0 +
    226 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 22 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (226 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_226 :
    recurrence5Scalar1Second.coeff 226 =
      -((((((1415576695 * 10 ^ 70 +
        9818708736974207452112443482741890692202776005868641214659404962383252) * 10 ^ 70 +
        6646657073502534420377195684133624364377602280084805599215203064111222) * 10 ^ 70 +
        4327456001287888234659424999439142980652537524935073891407325994406999) * 10 ^ 70 +
        4864768382542061571078296734962402997127377910539361528302241894106244) * 10 ^ 70 +
        8931462627546867937342357713592046449295337696778077578532499680750267) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 227 = 0 +
    227 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 22 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (227 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_227 :
    recurrence5Scalar1Second.coeff 227 =
      ((((((1059343065 * 10 ^ 70 +
        4581453702569377045136570543809325846394905396485729426027624755770558) * 10 ^ 70 +
        6644206392531782240491454020487239051840615399779568368838101727128392) * 10 ^ 70 +
        8363777381264241447758068045029038164667645220241961493487890138635236) * 10 ^ 70 +
        2255585734632799573918092437053495185459572726184502983465993129384692) * 10 ^ 70 +
        9310122259452754377919849560087265317120196892560948196096170578017661) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 228 = 0 +
    228 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 22 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (228 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_228 :
    recurrence5Scalar1Second.coeff 228 =
      -((((((778490470 * 10 ^ 70 +
        1592927181277409702650666075150578399818037909135702477240908267206918) * 10 ^ 70 +
        3872734048078434077616641879883419928547273314080428207584342403279724) * 10 ^ 70 +
        5324533365964463127829618594922980767825224248465259226719170480055428) * 10 ^ 70 +
        4228695879295754137659147669471204584777574529013992163302865300524624) * 10 ^ 70 +
        5976362027788227902295622615584219836519406903314250316851044085180221) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 229 = 0 +
    229 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 22 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (229 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_229 :
    recurrence5Scalar1Second.coeff 229 =
      ((((((561686627 * 10 ^ 70 +
        4138571465355693427013183784346401224092145535360450773051314616554389) * 10 ^ 70 +
        3148793102970270175610117303672558687800385997037303882625669072929507) * 10 ^ 70 +
        8485898817024405371718718954426532336161902271858513998303208510659970) * 10 ^ 70 +
        2866927966314755282633124454573563921034995108164617985678906046911040) * 10 ^ 70 +
        2836380109413429127208674575080773427763116009258536384580918240402364) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 230 = 0 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 22 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (230 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_230 :
    recurrence5Scalar1Second.coeff 230 =
      -((((((397811529 * 10 ^ 70 +
        2575719971829417382820695642247878855331917527197693934453385394189441) * 10 ^ 70 +
        7538186223746160368969344098075533288638390965342331465750827302138470) * 10 ^ 70 +
        3427419573852922597510511528144052941686887281650429044615344426041926) * 10 ^ 70 +
        0972537662390751299848594785282682345650339439040462706412777305308713) * 10 ^ 70 +
        8349456261618034458922608532284986904258038414781624809502067436641745) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 231 = 0 +
    231 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 22 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (231 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_231 :
    recurrence5Scalar1Second.coeff 231 =
      ((((((276523902 * 10 ^ 70 +
        1880998819256607129873422984408735625779502173798944421265899810653475) * 10 ^ 70 +
        1001881082335877335757678654954730200786855982018488337272292029054697) * 10 ^ 70 +
        3929020010411383788325052597741021310584272107746498764646525610797381) * 10 ^ 70 +
        2872802655256458457982224164597834008101828667504782323485447043182020) * 10 ^ 70 +
        0221441975235432492752917731196090776087863144896031699340962394296287) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 232 = 0 +
    232 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 22 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (232 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_232 :
    recurrence5Scalar1Second.coeff 232 =
      -((((((188626050 * 10 ^ 70 +
        3269065665793287779578847392833035650470178916199446619296063233881694) * 10 ^ 70 +
        4981157453164124685573717199092551424430711339209566486432090246851445) * 10 ^ 70 +
        7696269444841470264779668050889893265049108251267798991789142374072043) * 10 ^ 70 +
        1684443183684805937236985268829247349229801958704368330473246961887414) * 10 ^ 70 +
        9087345355857015881037814112890462475010021515024463232869753090390775) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 233 = 0 +
    233 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 22 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (233 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_233 :
    recurrence5Scalar1Second.coeff 233 =
      ((((((126250438 * 10 ^ 70 +
        9986895421064852688582480585693972806803803188324382427192411178969881) * 10 ^ 70 +
        6485483369094503545741176606236824096289143094866270458332073027495278) * 10 ^ 70 +
        9861368805025899977514758465771067820704616897210267447704997746182901) * 10 ^ 70 +
        3647973039148291037302952098762368922547644065730586879482736743481106) * 10 ^ 70 +
        9984236174651920361021402839301764496225599528955327099098667682061097) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 234 = 0 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 22 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (234 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_234 :
    recurrence5Scalar1Second.coeff 234 =
      -((((((82901697 * 10 ^ 70 +
        4691112951295837338153214903107634340368977263501289884048905847208687) * 10 ^ 70 +
        8467440607211641176594244931968256525471695460800686042710160594961833) * 10 ^ 70 +
        4908523687245720126384746244736575082115973608548606904905083914056176) * 10 ^ 70 +
        5534368690989217866297132335968494944274019018548538793711880843024462) * 10 ^ 70 +
        0922994185130910920101222738555507002517025470696981418377026305936651) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 235 = 0 +
    235 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 22 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (235 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_235 :
    recurrence5Scalar1Second.coeff 235 =
      ((((((53391841 * 10 ^ 70 +
        9972363838326012373402086672167319646585541529977220167549657068143960) * 10 ^ 70 +
        0733652067083119226439073263108604514980722740345533490092681989597242) * 10 ^ 70 +
        7027658337591083859521681897167419668677977388070740082467371955578375) * 10 ^ 70 +
        6593250242405349225232373263843917944281174308451926947516678111047771) * 10 ^ 70 +
        0895141915211993135400326760919809146379187298841093563106818402888146) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 236 = 0 +
    236 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 22 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (236 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_236 :
    recurrence5Scalar1Second.coeff 236 =
      -((((((33705624 * 10 ^ 70 +
        7088457148822611464208389652829932810817403425437234935095904604485674) * 10 ^ 70 +
        9757310891238375001976231533771191569480067433461385886497228061319525) * 10 ^ 70 +
        8721513083514284270204948277333122004474279936278627680947726857392552) * 10 ^ 70 +
        4095495021748077762156416964410281761809897251848410324501287229638246) * 10 ^ 70 +
        2764639673163407487944761067009546470431311096008675715396553330426577) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 237 = 0 +
    237 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 22 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (237 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_237 :
    recurrence5Scalar1Second.coeff 237 =
      ((((((20828477 * 10 ^ 70 +
        4960257733320825506852632277864623260137811594853869262078036869642011) * 10 ^ 70 +
        3410538057682908585735327951631474202093951134974718545396982469548103) * 10 ^ 70 +
        8959776540425367364452463009835544628965850214230350664785713950217093) * 10 ^ 70 +
        2121567803525918448698657884220832609622724688325642241970483367755057) * 10 ^ 70 +
        0276057441157270388960750585196492198585354795523236167752268825212110) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 238 = 0 +
    238 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 22 +
      88 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (238 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_238 :
    recurrence5Scalar1Second.coeff 238 =
      -((((((12563044 * 10 ^ 70 +
        4347702523130184044066418250979141740174474639411876917341106885092624) * 10 ^ 70 +
        3121333116425372853100642875796916376287632082386018396066694328201290) * 10 ^ 70 +
        4476994233612496934847005126772030740485457393186437549889152369768826) * 10 ^ 70 +
        4346483705670229135097451404520791403414178136427993383457808669580094) * 10 ^ 70 +
        8817041945716936197184267617776900892062199870135132543638803141995672) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 239 = 0 +
    239 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 22 +
      89 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (239 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_239 :
    recurrence5Scalar1Second.coeff 239 =
      ((((((7353105 * 10 ^ 70 +
        2518044848621377216721636717999680762536925039682370954308139262822987) * 10 ^ 70 +
        6422916998180752797550391515557844488477354239806909454720940109036881) * 10 ^ 70 +
        8535541319553283601664127596782133631285342815323542248900288219403937) * 10 ^ 70 +
        9893238010211201466074240618194576190711787427331486690821934300215946) * 10 ^ 70 +
        9705276010768446194581135189282569243420976947793334510320261132090870) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 240 = 0 +
    240 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 22 +
      90 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (240 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_240 :
    recurrence5Scalar1Second.coeff 240 =
      -((((((4126812 * 10 ^ 70 +
        5058154788710736307804725215848070712259014389831790131008327840683900) * 10 ^ 70 +
        1103722259997472097781841213746800922110064066651902332136083754276077) * 10 ^ 70 +
        1121654832998477127857507074873518159436587587457695528550295074371144) * 10 ^ 70 +
        2974319664924527522895235834023400251880489035551773015480052926254973) * 10 ^ 70 +
        4083408783851964514754610828105098083809900831934928928391219914804484) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 241 = 0 +
    241 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 22 +
      91 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (241 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_241 :
    recurrence5Scalar1Second.coeff 241 =
      ((((((2165278 * 10 ^ 70 +
        7211453627359593293188569018988849805525564418237061317105535110157290) * 10 ^ 70 +
        6787937184233002565680542665694997385529557906392962079290874512631213) * 10 ^ 70 +
        1308419633824003579204151755833967447661098900454099589850529226454473) * 10 ^ 70 +
        9473426861829418706084363488289615608351913600641787171892912756804458) * 10 ^ 70 +
        6527500475352596823219316106559710474573207147535560447606806970509756) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 242 = 0 +
    242 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 22 +
      92 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (242 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_242 :
    recurrence5Scalar1Second.coeff 242 =
      -((((((998008 * 10 ^ 70 +
        7287325593030876893268825586019768127248442626586703575909293561378871) * 10 ^ 70 +
        0808403058415687525518165651435130597695037449825292841605057397144923) * 10 ^ 70 +
        7658988095440340487425262830121228882275950969825670905611050376256832) * 10 ^ 70 +
        0452396597921777883621726192527627960734536463920015084369583081763153) * 10 ^ 70 +
        1305942646762688392669936281561373017702613243756633508932032649813625) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 243 = 0 +
    243 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 22 +
      93 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (243 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_243 :
    recurrence5Scalar1Second.coeff 243 =
      ((((((323552 * 10 ^ 70 +
        9891147855332790745993840764272413848909806353085685434788995310040241) * 10 ^ 70 +
        4885690039709166768425878390989018181519185212110916240958565761247197) * 10 ^ 70 +
        4423661221928680821497393162726986203874786181637179853459509398525816) * 10 ^ 70 +
        5498844089958447204630292290346940073650011230639006976248331800778267) * 10 ^ 70 +
        3589572406095535102056673058541995601762427531380791203183697321112925) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 244 = 0 +
    244 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 116 = 22 +
      94 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (244 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_244 :
    recurrence5Scalar1Second.coeff 244 =
      ((((((48064 * 10 ^ 70 +
        5014782653923872269452270619338746750319638614755436562083506480462992) * 10 ^ 70 +
        5745385989843988728980150127574890129825530559220622467924263664972316) * 10 ^ 70 +
        5607061363384219027951990714880238635678526162298481624998861061506784) * 10 ^ 70 +
        6210456243068515556168020167583816577873818565067281696970801682739358) * 10 ^ 70 +
        2662931425978397216016667027130728661976625660324695030872811020140394) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 245 = 0 +
    245 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 117 = 22 +
      95 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (245 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_245 :
    recurrence5Scalar1Second.coeff 245 =
      -((((((235359 * 10 ^ 70 +
        3797205436558151976022831112714273133853144700573070483475013170846530) * 10 ^ 70 +
        6069560679337163598244015245994675830248293605953409352745875834661558) * 10 ^ 70 +
        4967428808982668853302186167868664578348266028189561678013245411352993) * 10 ^ 70 +
        2672330608461672116553606084325258114001232242486999447964187675099760) * 10 ^ 70 +
        4247428844058622550141913108197474124350476174392162000795723572696340) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 246 = 0 +
    246 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 118 = 22 +
      96 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (246 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_246 :
    recurrence5Scalar1Second.coeff 246 =
      ((((((312066 * 10 ^ 70 +
        0007075274545928961109512494869599273684909287378391455976164237886320) * 10 ^ 70 +
        6644779308524801630558107379971783593743743129945103059675103788501328) * 10 ^ 70 +
        7852444265205483169219546639726639309954847886368765377612017231776951) * 10 ^ 70 +
        9772322799139416349283533091558105305952484284339117291112316777036391) * 10 ^ 70 +
        7552156311822427491294627240068694020258703996886557959468364186833438) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 247 = 0 +
    247 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 119 = 22 +
      97 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (247 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_247 :
    recurrence5Scalar1Second.coeff 247 =
      -((((((324242 * 10 ^ 70 +
        0591516385382489110859585575255513518090470142769305173943268816292174) * 10 ^ 70 +
        0171942491022854547566227951647222771757761637648535676106495958442960) * 10 ^ 70 +
        0675864921225054390686652469444330999747357368847874025746076098770835) * 10 ^ 70 +
        3439440758736014687076993125540989442762079300067784881868742219550010) * 10 ^ 70 +
        8459374010659810237125374778979181164282854412403249240842313834608928) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 248 = 0 +
    248 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 120 = 22 +
      98 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (248 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_248 :
    recurrence5Scalar1Second.coeff 248 =
      ((((((300860 * 10 ^ 70 +
        8461247266584051405145432840710033510954215996912898240231252799175336) * 10 ^ 70 +
        2260743576863093104948394453863017647109494937678328841338836289838440) * 10 ^ 70 +
        3406871138731786977507198752825537230266627297049279538787320004659937) * 10 ^ 70 +
        3172524583736947371738032804473074160907260343501305469019786862152056) * 10 ^ 70 +
        5943567109287943601827827300235928559588256946943936542660259148967424) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 249 = 0 +
    249 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 121 = 22 +
      99 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (249 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_249 :
    recurrence5Scalar1Second.coeff 249 =
      -((((((260204 * 10 ^ 70 +
        1311794371339976782214558557742688563449244472542772524860185673500417) * 10 ^ 70 +
        7386392368430309635399562476604410072705341583836711180148800601209047) * 10 ^ 70 +
        9521109030816659098371569277532750809267285205491231606597651629956738) * 10 ^ 70 +
        6465748213238055905027201236648513911958281533669551931303935540676468) * 10 ^ 70 +
        8990373886030206351400070996241528768476930373444668877959629812006948) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 250 = 0 +
    250 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 122 = 22 +
      100 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (250 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_250 :
    recurrence5Scalar1Second.coeff 250 =
      ((((((213684 * 10 ^ 70 +
        5694661831580035404619180399471893500481673298844371592782331646411531) * 10 ^ 70 +
        3086034167775778889514904352456806209645112837029955223918307057146470) * 10 ^ 70 +
        2383659058271477243292448156453847723242485915297647442759575865711864) * 10 ^ 70 +
        4630317170015056496780236537098259896908279135921093427011819105918954) * 10 ^ 70 +
        6949838726154618346344049233537898309896514722175513785876952578643964) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 251 = 0 +
    251 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 123 = 22 +
      101 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (251 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_251 :
    recurrence5Scalar1Second.coeff 251 =
      -((((((168167 * 10 ^ 70 +
        7753203704125704647118816429363676039343149576077697213883344915481936) * 10 ^ 70 +
        1539852545518842695121543799831495608481631836340521302710684675166012) * 10 ^ 70 +
        5970021018431746402825555864836934319848281961298219435829822075709147) * 10 ^ 70 +
        2152051694784507552233366519696191095057059356663926746127406816146735) * 10 ^ 70 +
        5016082391107088139086554684116889209798785834776344352605511329479718) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 252 = 0 +
    252 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 124 = 22 +
      102 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (252 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_252 :
    recurrence5Scalar1Second.coeff 252 =
      ((((((127448 * 10 ^ 70 +
        2101747699837810150649622792086179620078961799596432081757626696936846) * 10 ^ 70 +
        1242444132460229573843149289270242324928213822284495042700853202532182) * 10 ^ 70 +
        7235581065645885158233948118799631792050822913175907037826565365902931) * 10 ^ 70 +
        7174947543766738541133610283616627183836662830020140589433782944602846) * 10 ^ 70 +
        1050314583192539006149341747504071018912926416487675688924466092581428) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 253 = 0 +
    253 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 125 = 22 +
      103 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (253 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_253 :
    recurrence5Scalar1Second.coeff 253 =
      -((((((93249 * 10 ^ 70 +
        2465333837700435325173111011249234014895504610619275654448149244690769) * 10 ^ 70 +
        1158957848424374804425013577812849671962060958058213631454648036936521) * 10 ^ 70 +
        2709628398746617186967696750105222357029742049048870224196717533974750) * 10 ^ 70 +
        7349688501289124335934673569582702027486014496844250179814489011579986) * 10 ^ 70 +
        3353869287162440612380112454352412252872978471703238808425144070463636) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 254 = 0 +
    254 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 126 = 22 +
      104 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (254 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_254 :
    recurrence5Scalar1Second.coeff 254 =
      ((((((65941 * 10 ^ 70 +
        0452879929095953068662320403245152666176076766504300927970664380993351) * 10 ^ 70 +
        5205143399020700551128405788032037558501903675564011752713573498260250) * 10 ^ 70 +
        1448288142256186961458062762716014721920546891268891422716775503663808) * 10 ^ 70 +
        2147683830874603794465613034138090521384052076336630984524524403336320) * 10 ^ 70 +
        8090084546230445555448713059390045707964768056751862007431437354175042) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 255 = 0 +
    255 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 127 = 22 +
      105 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (255 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_255 :
    recurrence5Scalar1Second.coeff 255 =
      -((((((45070 * 10 ^ 70 +
        7520423631996774869891960218071209872079149074802820285115773980936703) * 10 ^ 70 +
        1856744910318515633213701088937895292024335045226416922917393406134412) * 10 ^ 70 +
        9742739984826683330421537826355371684262694477122056828962274058235148) * 10 ^ 70 +
        3295576739712489851904606150651835594091224742576186597782485740650616) * 10 ^ 70 +
        4023336374027437960223808022251565841582924593825672950116251707074055) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 256 = 0 +
    256 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 128 = 22 +
      106 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (256 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_256 :
    recurrence5Scalar1Second.coeff 256 =
      ((((((29750 * 10 ^ 70 +
        8295210814976233042524248003873871503581989618475277572579034256133536) * 10 ^ 70 +
        6510526570048151562458704864388095453285763502615654874852606624971004) * 10 ^ 70 +
        6688352146737806759276725117571201736163883783279813834421032816801759) * 10 ^ 70 +
        3583096602217804192831368944802474667421797099325756881072527201483557) * 10 ^ 70 +
        6592096445776464836168964216198183920034536593963551283480815148858632) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 257 = 0 +
    257 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 129 = 22 +
      107 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (257 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_257 :
    recurrence5Scalar1Second.coeff 257 =
      -((((((18931 * 10 ^ 70 +
        6262197952279786431803775746597995870190025556471840620085949559893758) * 10 ^ 70 +
        0071622366514698085684123159649895219246117424483140294766565528234810) * 10 ^ 70 +
        5468806257419560149501682516223500929833571198055973123892563854020392) * 10 ^ 70 +
        8060846869836199699239162751892934854718291841948279768788990004483423) * 10 ^ 70 +
        1160398281672330596990570263358026079814977588890792743660358876243283) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 258 = 0 +
    258 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 130 = 22 +
      108 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (258 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_258 :
    recurrence5Scalar1Second.coeff 258 =
      ((((((11578 * 10 ^ 70 +
        6184407113968021230483955051896591551976510584998344681440814166202220) * 10 ^ 70 +
        1190203804647758272196864148306206131752967189393097435945598846932062) * 10 ^ 70 +
        2232455867994724175252080305785039802799418177720807241870452001503618) * 10 ^ 70 +
        5499531241859919303726506187390674416699786497443863003948529137250048) * 10 ^ 70 +
        1346139513463420270704355145753169587799639992861932214066294265016133) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 259 = 0 +
    259 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 131 = 22 +
      109 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (259 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_259 :
    recurrence5Scalar1Second.coeff 259 =
      -((((((6774 * 10 ^ 70 +
        1075203246988008933018821556212117031727518708859640018819594585325671) * 10 ^ 70 +
        4083051147941404006260003448651440652135119629001831220628554742164941) * 10 ^ 70 +
        2717368762533887657060934865802602144423414046188492877644792570779805) * 10 ^ 70 +
        0337459544703453172794505786187026803280152462964440862752948428025983) * 10 ^ 70 +
        8202664678027568567086252557694450398527046487301509911990758095126381) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 260 = 0 +
    260 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 132 = 22 +
      110 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (260 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_260 :
    recurrence5Scalar1Second.coeff 260 =
      ((((((3762 * 10 ^ 70 +
        9176921142197125234591334994409221071956472907904693379831291814355684) * 10 ^ 70 +
        1958786902637795513752094572114468993006759052160792484707435432202907) * 10 ^ 70 +
        3032557905132732788524752779764659863785742460763951720582271293089308) * 10 ^ 70 +
        4830595984374647792517643381883859460829020973332582714106676661907701) * 10 ^ 70 +
        6374105134266098905808291073489710212214386256084296560613153853357821) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 261 = 0 +
    261 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 133 = 22 +
      111 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (261 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_261 :
    recurrence5Scalar1Second.coeff 261 =
      -((((((1960 * 10 ^ 70 +
        1491511209769705145153768185195399697976288211427339913076363409033080) * 10 ^ 70 +
        4983774894020754519763129096639236420353115947977839542479110381144836) * 10 ^ 70 +
        6115880840821310314446896590589536403740357329095066570573003717256217) * 10 ^ 70 +
        8395393471562033617374067979609035552317739333062782228314099753012849) * 10 ^ 70 +
        1893342813388460190351971384702956332357578070343140696515128485363772) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 262 = 0 +
    262 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 134 = 22 +
      112 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (262 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_262 :
    recurrence5Scalar1Second.coeff 262 =
      ((((((936 * 10 ^ 70 +
        2228911095030412635117882855422197942287044691218017785787681825319505) * 10 ^ 70 +
        3794960543416801035779929983336431563936692897394723033041703231909410) * 10 ^ 70 +
        6490359319923487419891231002176423527576295411664633934964225218762891) * 10 ^ 70 +
        0572268129783509027787556422653816559312934289500421498400095136338217) * 10 ^ 70 +
        2868451202306656643069793856563816497818285203894003690631555759524987) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 263 = 0 +
    263 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 135 = 22 +
      113 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (263 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_263 :
    recurrence5Scalar1Second.coeff 263 =
      -((((((390 * 10 ^ 70 +
        8963835487216530439063707731100887392469889047636867279150916991625277) * 10 ^ 70 +
        2541113497477502511954700763419959269866818306070421196799215528678467) * 10 ^ 70 +
        6054072187770801937059488435442872292025180007248992591032895272546952) * 10 ^ 70 +
        9689175773154088436493159360370226135404709644396526676412411690026674) * 10 ^ 70 +
        7691811763007997709978795915163235431141119293305435803112766364886374) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 264 = 0 +
    264 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 136 = 22 +
      114 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (264 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_264 :
    recurrence5Scalar1Second.coeff 264 =
      ((((((124 * 10 ^ 70 +
        3137834179435465635819306168815703549222403193032184471810124198948797) * 10 ^ 70 +
        8697225250570747143771788523718508980018227462387055436956362772154511) * 10 ^ 70 +
        1235158792870515931140580637893206729227273366786770177387819879420264) * 10 ^ 70 +
        3843449777792899126899314108481766769620700918298799084602210463791176) * 10 ^ 70 +
        6815814083324220360678548849968672726943327605086347509338433330738060) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 265 = 0 +
    265 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 137 = 22 +
      115 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (265 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_265 :
    recurrence5Scalar1Second.coeff 265 =
      -((((((9 * 10 ^ 70 +
        9882128069152051868500558173103428544970096424551992635502655475716396) * 10 ^ 70 +
        6615435581188092806954415113210458625483882086773824646882333038669594) * 10 ^ 70 +
        5891054922689108969073353495893159042901683086189379950177536665567009) * 10 ^ 70 +
        3740770901196125165279204735434218324799305511867394842614585990437958) * 10 ^ 70 +
        5316316218570270050963380736137598067702093230372793805188924818411368) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 266 = 0 +
    266 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 138 = 22 +
      116 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (266 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_266 :
    recurrence5Scalar1Second.coeff 266 =
      -((((((27 * 10 ^ 70 +
        8420853517245567823096933331791337059136386769106828489447100286280010) * 10 ^ 70 +
        0707901090337071372102368628763072579117478869232886511954442039229500) * 10 ^ 70 +
        8900529516151168571963491935863200132177288934355255253493774357965622) * 10 ^ 70 +
        6549181677238995632479234668442409704602633663216958136775362786362773) * 10 ^ 70 +
        2404841496485842367028793137124661892545481824187261614160141950495532) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 267 = 0 +
    267 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 139 = 22 +
      117 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (267 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_267 :
    recurrence5Scalar1Second.coeff 267 =
      ((((((31 * 10 ^ 70 +
        7379548441622396406417329900484254571998190859602678154797477108636995) * 10 ^ 70 +
        3634406642334705054475001746301104818515813762024764356309440339714536) * 10 ^ 70 +
        5265550341617533741121373839558551676670734561521046215478975329932624) * 10 ^ 70 +
        0591931501285534474322278517608638941259512479632221061451657007186015) * 10 ^ 70 +
        9307555924650681547700059433926323701796434748963852976533116629991762) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 268 = 0 +
    268 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 140 = 22 +
      118 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (268 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_268 :
    recurrence5Scalar1Second.coeff 268 =
      -((((((23 * 10 ^ 70 +
        7433240317734554181541623206096638141856114961295653339296176966904215) * 10 ^ 70 +
        2465919575057743819970595590214290939880973098255705531435588724835801) * 10 ^ 70 +
        6684115961786910298447059662198660040650814466438003028484031000278730) * 10 ^ 70 +
        8664193119681310505169386929102151473513783744327861015986167984249368) * 10 ^ 70 +
        4483355542284783772420532088766404645854004465055508284420299017400493) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 269 = 0 +
    269 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 141 = 22 +
      119 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (269 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_269 :
    recurrence5Scalar1Second.coeff 269 =
      ((((((14 * 10 ^ 70 +
        0169335201935102580790607925778752064028403006886378313740091449344966) * 10 ^ 70 +
        6830282203313193707493587988971204374398683957739616511610887856730239) * 10 ^ 70 +
        4086905727156078366317908104558717391689940467326392831925876154269622) * 10 ^ 70 +
        9871005060860246062732549422547327243390140859122740323790256809939296) * 10 ^ 70 +
        7429179788283169035955679734593989032233242500365486610463563370034659) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 270 = 0 +
    270 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 142 = 22 +
      120 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (270 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_270 :
    recurrence5Scalar1Second.coeff 270 =
      -((((((6 * 10 ^ 70 +
        3563734331981422976607406501391692486399129374914753559938334299206581) * 10 ^ 70 +
        4678461687452000226518830937813978374951095768316907439054000560635168) * 10 ^ 70 +
        0552776765887611510382867607023573996278637452579348035269415004825857) * 10 ^ 70 +
        4374384511612345296798794355575239434532392402135746120187002608615671) * 10 ^ 70 +
        3447458777863346597212426439030465819423278972171862095282225039977533) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 271 = 0 +
    271 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 143 = 22 +
      121 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (271 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_271 :
    recurrence5Scalar1Second.coeff 271 =
      ((((((1 * 10 ^ 70 +
        5070023986997796845079968449824336071468131823521108285736676365351739) * 10 ^ 70 +
        7690608855495635672247848815877266047272688589275717693816840864218395) * 10 ^ 70 +
        5091728679925916178620281270318029689901942935548293502314773338799222) * 10 ^ 70 +
        8209884438891966414503547498741460280452588798851847294318768618206175) * 10 ^ 70 +
        6174948089617174036433910208554376300520330657885029091511835973114242) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 272 = 0 +
    272 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 144 = 22 +
      122 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (272 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_272 :
    recurrence5Scalar1Second.coeff 272 =
      ((((((1 * 10 ^ 70 +
        0043029066427330112615620704866310623873033142690865791431558326275871) * 10 ^ 70 +
        9578881632124900441483270361438906028202097055691961106997791318882452) * 10 ^ 70 +
        7208129997774139338456645944848869389662937693886129393128775411531831) * 10 ^ 70 +
        9457327616207971583399883549751291773669892379583211404192270890950393) * 10 ^ 70 +
        2096844970812714781196158191214614428770328775597128466456637540114690) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 273 = 0 +
    273 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 145 = 22 +
      123 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (273 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_273 :
    recurrence5Scalar1Second.coeff 273 =
      -((((((1 * 10 ^ 70 +
        9520463730657930762456122546288080490618241245811170566523527305724504) * 10 ^ 70 +
        9834781944436622143272465517231307745530930689022281515210543756229418) * 10 ^ 70 +
        8751955582809251858449945273451911104287884471745871244633660411577165) * 10 ^ 70 +
        4247237334565780081334171565658390484390208332957631969609868513334356) * 10 ^ 70 +
        0945026132984319859838214754949667308293030851174894472792588076708826) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 274 = 0 +
    274 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 146 = 22 +
      124 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (274 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_274 :
    recurrence5Scalar1Second.coeff 274 =
      ((((((2 * 10 ^ 70 +
        0220569120837512984592649695201588078365637410174032311772363383820985) * 10 ^ 70 +
        5423362354408243290247326801725204850063950836819447077497050417475733) * 10 ^ 70 +
        0984338249655064870736248120250256039101755097087007308640327949329084) * 10 ^ 70 +
        1685644528394290440403862514726713226631430643487332589706553977989775) * 10 ^ 70 +
        7809964400194681954603815600167482282037471278476728417532092603336901) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 275 = 0 +
    275 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 147 = 22 +
      125 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (275 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_275 :
    recurrence5Scalar1Second.coeff 275 =
      -((((((1 * 10 ^ 70 +
        6963152370226966366804169653349210650669414392097474088363076722453571) * 10 ^ 70 +
        4962556171734433233696305528547701895017392793529429505825336661710311) * 10 ^ 70 +
        9225506000163043599589822885001272982188722853253735206637808664878634) * 10 ^ 70 +
        4392834282072553548249469956916667127145541000581722004985564145688392) * 10 ^ 70 +
        5126396932338229448828889062150150405623029914139444374724271609436024) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 276 = 0 +
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
    rw [show 148 = 22 +
      126 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (276 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_276 :
    recurrence5Scalar1Second.coeff 276 =
      ((((((1 * 10 ^ 70 +
        2618873042191992062882209943510245550467434698386923758682293203503177) * 10 ^ 70 +
        9822933489840009483475380973505250887147715527228837948344744366595327) * 10 ^ 70 +
        1815024816643383129762242505257392641832954774068700194331611715702927) * 10 ^ 70 +
        0064385822768671622490758649441830005204626723060184076551332127639075) * 10 ^ 70 +
        6334968242346723067369986813702016331706947165007273104987213167604323) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 277 = 0 +
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
    rw [show 149 = 22 +
      127 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (277 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_277 :
    recurrence5Scalar1Second.coeff 277 =
      -(((((8619190732514507127175396356182875829301721457273326136044114511887189 * 10 ^ 70 +
        7530935184328786195806163714773524939442325242575590351256321098765787) * 10 ^ 70 +
        6655582173245515607955336715112555158843788821854943668101643829838752) * 10 ^ 70 +
        5470639878440767964913187789813537500400698356503150920762000268957216) * 10 ^ 70 +
        2290937928403379227620780930483841997742011579013467977269118831657868) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 278 = 0 +
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
    rw [show 150 = 22 +
      128 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (278 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_278 :
    recurrence5Scalar1Second.coeff 278 =
      (((((5495140391643861964627227576021049800833796576176898526489401896543218 * 10 ^ 70 +
        6083648196949802315122438035216876593594690276805058766366265968119600) * 10 ^ 70 +
        3456380963071807745547500720624223243538119901347697080783817483725968) * 10 ^ 70 +
        5248746393137183556659366478680874048835043356463543929718521012726146) * 10 ^ 70 +
        1075671979762416106410835859921654787653263331767289944950179191564415) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 279 = 0 +
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
    rw [show 151 = 22 +
      129 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (279 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_279 :
    recurrence5Scalar1Second.coeff 279 =
      -(((((3296716238857651820400102601493249812748109138026173255052259885680887 * 10 ^ 70 +
        3080084816354494520996431532938513190445112216133126154831439227608211) * 10 ^ 70 +
        9897524800184882877081916546684033628316523955225306811227057521830095) * 10 ^ 70 +
        6516841985223613543888879848603836251867331136082105005108734348781305) * 10 ^ 70 +
        6270747033404420820781531416770260926818399302278835613898859081591117) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 280 = 0 +
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
    rw [show 152 = 22 +
      130 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (280 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_280 :
    recurrence5Scalar1Second.coeff 280 =
      (((((1867278365094381065033698219477865291632863475820881279113372036413107 * 10 ^ 70 +
        9619460590062445251894064750342811537538302136158558108348264719822493) * 10 ^ 70 +
        5586337602169755599803468920294229595516963852409378172746604094557722) * 10 ^ 70 +
        7733553470495098367622060908580598190130110143653175398045972089995574) * 10 ^ 70 +
        7193719873732539303823155196706436678771020857368457231220851637837930) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 281 = 0 +
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
    rw [show 153 = 22 +
      131 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (281 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_281 :
    recurrence5Scalar1Second.coeff 281 =
      -(((((998174391349510477504148680029187386143116053835859446007611324490592 * 10 ^ 70 +
        1672177641460687083506498870627015936090524936041435106991978424706880) * 10 ^ 70 +
        3739994431722171577939716982917408701097077403598908319653539730691427) * 10 ^ 70 +
        7063923964786394871824463301257063396560339384017020130352561050070614) * 10 ^ 70 +
        5248304761925546429368073552701142079450834672432539978168522867513901) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 282 = 0 +
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
    rw [show 154 = 22 +
      132 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (282 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_282 :
    recurrence5Scalar1Second.coeff 282 =
      (((((501486717706490661293378201015030507039715094247756062345559072428448 * 10 ^ 70 +
        4483317553516487656613797687162062234665998349660448189675568717603567) * 10 ^ 70 +
        3590034366472112933191775229499106788920073868142443629621644784957216) * 10 ^ 70 +
        8593313891408346876534055006085561233833206132378215974759721513708452) * 10 ^ 70 +
        0037552347288008100100778552591993294119517899970015292872376010737200) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 0 +
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
    rw [show 155 = 22 +
      133 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (283 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_283 :
    recurrence5Scalar1Second.coeff 283 =
      -(((((234524510716514679835878768570937555539554540740362768392367529223346 * 10 ^ 70 +
        5941685711015051855550983472286186333249957065312137300904596334350676) * 10 ^ 70 +
        5418101591690793481463607180906027265775556246298460125635947455096213) * 10 ^ 70 +
        1163670308880907119868676873323574517869982368038462053286677201144201) * 10 ^ 70 +
        7772058108981330722356640533352720509243641948562944657917382144703028) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 0 +
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
    rw [show 156 = 22 +
      134 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (284 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_284 :
    recurrence5Scalar1Second.coeff 284 =
      (((((100094373829418950102484297272229071364437507052053299396647474166622 * 10 ^ 70 +
        5419793779341338004081728839446222297310166318812628067636263664018806) * 10 ^ 70 +
        6540640102379462324296680337390506631823585027674815130277051200961726) * 10 ^ 70 +
        2161307808153498067461607267307042419680769049806410733274364216342658) * 10 ^ 70 +
        0719049551234517699354320423459471558078791590167547816548085135497165) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 0 +
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
    rw [show 157 = 22 +
      135 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (285 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_285 :
    recurrence5Scalar1Second.coeff 285 =
      -(((((37300480129883958346886735511500502767402388156222757142320735092215 * 10 ^ 70 +
        2999750791726684519668437578648474447157387889942132064129354887580477) * 10 ^ 70 +
        8783047202571060724827883834787372765529254662840995415868774066488460) * 10 ^ 70 +
        9461281299731482802954556438579783239914728744435758672328470531165540) * 10 ^ 70 +
        9934109581568805971352903680173675090658199778737559140930609642228220) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 0 +
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
    rw [show 158 = 22 +
      136 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (286 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_286 :
    recurrence5Scalar1Second.coeff 286 =
      (((((10661105064687579893173047317239013215583259570323761136848892271991 * 10 ^ 70 +
        6646020112136228782548778139937663161209678758480971776224832611085569) * 10 ^ 70 +
        7803142133198032075852712459871869259892509290587658480705994403239869) * 10 ^ 70 +
        5121343853125894749434603165367826139538649150558939915847003231984981) * 10 ^ 70 +
        6994994255584116991069604980710534588596129241091860708860357737345702) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 0 +
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
    rw [show 159 = 22 +
      137 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (287 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_287 :
    recurrence5Scalar1Second.coeff 287 =
      -(((((886985016370146543865490932048314073400795046918723658576122137177 * 10 ^ 70 +
        0894642662608178858289726216762197243757236512562158678154284505317993) * 10 ^ 70 +
        5393779566020381592175508128874437425382380478513760743492424473798260) * 10 ^ 70 +
        8039678108047119511821120318740530538429740434225605553619237003021853) * 10 ^ 70 +
        3096081466373270785380422075601022412239181939650997760856017643023187) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 0 +
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
    rw [show 160 = 22 +
      138 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (288 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_288 :
    recurrence5Scalar1Second.coeff 288 =
      -(((((1778314576949148628998409091531898911795105309451332299901765903557 * 10 ^ 70 +
        0935068551091241794801931442025550857400032316373288069101380873693163) * 10 ^ 70 +
        4562421028719766537840840621942127081392214696998013869755562735116902) * 10 ^ 70 +
        8585119493701267864901607483623937986641559190976096711481692923259873) * 10 ^ 70 +
        3069491387481596609786829760954384317507042860771235558171602925198467) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 0 +
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
    rw [show 161 = 22 +
      139 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (289 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_289 :
    recurrence5Scalar1Second.coeff 289 =
      (((((1878606164988648468647134422106580369301329210805884445205148362135 * 10 ^ 70 +
        4897198625941895191044616253995031507399744787074294456349011817119070) * 10 ^ 70 +
        9616676079143753956963080728746088937626011717422733602379351167741124) * 10 ^ 70 +
        6336488852662605646543779101852473451530704410531232607923151485589793) * 10 ^ 70 +
        2189899663275412338930613594896420799106891676591533620890021036827175) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 0 +
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
    rw [show 162 = 22 +
      140 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (290 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_290 :
    recurrence5Scalar1Second.coeff 290 =
      -(((((1315849169117367255743636648611905636912648693803078996423156503206 * 10 ^ 70 +
        2706111286063121221691503409601371813374626260671001747750102743791576) * 10 ^ 70 +
        5278076853139413614525108327353309556850862540181516681159739340483746) * 10 ^ 70 +
        5976793532688294969434973288898575779677746077540151401396090743073707) * 10 ^ 70 +
        6292505808513632432395320748786077151079168861760074022542983883174866) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 0 +
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
    rw [show 163 = 22 +
      141 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (291 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_291 :
    recurrence5Scalar1Second.coeff 291 =
      (((((764017299513363930424893297083285584588882819367961304112972729081 * 10 ^ 70 +
        3489515092946631659437157234755478433849805067000255250425720198007181) * 10 ^ 70 +
        9957638884187398344550888387955195719255994914113129855416444540823732) * 10 ^ 70 +
        3308045149669265663302153724654679978244844233806330218457609599426869) * 10 ^ 70 +
        4759210938198994224056983079310032197521161480884785074990708942480772) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 0 +
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
    rw [show 164 = 22 +
      142 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (292 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_292 :
    recurrence5Scalar1Second.coeff 292 =
      -(((((386945875639474398018232709822122779850423669024008013223539072975 * 10 ^ 70 +
        0798950719250934023548882336358635189500379524515024462220673113901891) * 10 ^ 70 +
        0605517749125124772101884303250985663401959073849352952142389116482929) * 10 ^ 70 +
        6562664588632105652247689792450568264931926216298977625688037864623589) * 10 ^ 70 +
        9196330434024681205566885191125475445665129944892053664595127748341934) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 0 +
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
    rw [show 165 = 22 +
      143 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (293 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_293 :
    recurrence5Scalar1Second.coeff 293 =
      (((((171214282580295232635490546376304478213540098034702808857571501836 * 10 ^ 70 +
        9494869162569019613605007201428204610619231751371995950831806724783664) * 10 ^ 70 +
        2316379531140851639642901179489999560506385731416620949828633800450317) * 10 ^ 70 +
        8396799791925358008792411000541717378908155202072165624722255416077204) * 10 ^ 70 +
        1567616073479939904378841900455051044843100931120510757516315442777749) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 0 +
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
    rw [show 166 = 22 +
      144 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (294 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_294 :
    recurrence5Scalar1Second.coeff 294 =
      -(((((63294181977202050415012378419964553998820214371317428322527259733 * 10 ^ 70 +
        0839683257531611400743833256510203656922010838693085707401407436089247) * 10 ^ 70 +
        0414065394043742504791615000059065105038475319586250032437910923244232) * 10 ^ 70 +
        6711353492773195463792873144206465617113099446153162759853741814517193) * 10 ^ 70 +
        3287598922066009404873995539151055655344455849930705972175149832719397) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 0 +
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
    rw [show 167 = 22 +
      145 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (295 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_295 :
    recurrence5Scalar1Second.coeff 295 =
      (((((16191979373155021413497104001435089858826148709602190773807606840 * 10 ^ 70 +
        2570281597224253313792908012701493675134529999097539482401662114827500) * 10 ^ 70 +
        5532739782731762494808106652148868068276596389981025279281364156110389) * 10 ^ 70 +
        8873392327244729992300661699388668784584680055816570446410993951829837) * 10 ^ 70 +
        4719344572909555254018309480864914009970985833644344353950983570927081) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 0 +
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
    rw [show 168 = 22 +
      146 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (296 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_296 :
    recurrence5Scalar1Second.coeff 296 =
      (((((858927876527218335322699463783723784987571815018944962051813673 * 10 ^ 70 +
        7029493926588189203897422324379116453825830548993730503470785040027489) * 10 ^ 70 +
        6093837321790418461155061047767848044297738468356002123600661461043651) * 10 ^ 70 +
        9515814651725637954498941236086834794010844412333069637952570232532377) * 10 ^ 70 +
        4818987195535624754286683149269016300431531801893501726277529848897043) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 0 +
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
    rw [show 169 = 22 +
      147 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (297 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_297 :
    recurrence5Scalar1Second.coeff 297 =
      -(((((4979054441516278029026385632743729049278007187271127882291703240 * 10 ^ 70 +
        3859366113059218554084194929702058295431956903769916518416816041664361) * 10 ^ 70 +
        8406439145394266436734958908275451943023883186065918071248779388107101) * 10 ^ 70 +
        5350254886029918279002425887615619195058383980076737715161724104157550) * 10 ^ 70 +
        8791720694486596597116802657357813348812335420058512040017009882313335) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 0 +
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
    rw [show 170 = 22 +
      148 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (298 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_298 :
    recurrence5Scalar1Second.coeff 298 =
      (((((4523266359760295925755553256163602985452525097923114841207185589 * 10 ^ 70 +
        7415680289314440007932174414741928434814395870328942393948030851048905) * 10 ^ 70 +
        2333110816009177923744551079048821577595813684753926028847857209455606) * 10 ^ 70 +
        6532035073472456638818806747209867509203331125140208362297759747510674) * 10 ^ 70 +
        7638979342639821778813277094403845023697681809997386782890263893400326) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 0 +
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
    rw [show 171 = 22 +
      149 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (299 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_299 :
    recurrence5Scalar1Second.coeff 299 =
      -(((((3033462737808250837203728368690093550594110456567678463194532916 * 10 ^ 70 +
        2414177083461833778395533141505037361589783119830345406290703584380826) * 10 ^ 70 +
        1811257491519159018585752520058908869943620552323958356670483586502291) * 10 ^ 70 +
        5042973620806719483907404685530930328197783481426188231042060307841142) * 10 ^ 70 +
        3146775305853939568187080305314578221202648836963794794268633226891436) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 0 +
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
    rw [show 172 = 22 +
      150 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (300 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_300 :
    recurrence5Scalar1Second.coeff 300 =
      (((((1732415016648691551978049060728048020904310975931809649019953119 * 10 ^ 70 +
        6320946294930782589011294015286103334372345835946740424711609071260118) * 10 ^ 70 +
        6666944149451607147336601090095275657401786565663247410422739740280116) * 10 ^ 70 +
        2247882726597734140589253380892232668849444621394809366059596837173768) * 10 ^ 70 +
        1800638932176536683385001883915514095682099226172821649431393441679216) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 0 +
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
    rw [show 173 = 22 +
      151 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (301 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_301 :
    recurrence5Scalar1Second.coeff 301 =
      -(((((875051578890290148605394239083883223092689430277960250477099535 * 10 ^ 70 +
        3841195166202173184859538774672273659334529955423603637242176322032020) * 10 ^ 70 +
        0229304296218938804736699523980026382481038559543305523626698055812571) * 10 ^ 70 +
        5037533956264706701843523347709041609124128982282317554970663749743492) * 10 ^ 70 +
        6933083808498906703617497442491995615718776535173144412186813466181605) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 0 +
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
    rw [show 174 = 22 +
      152 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (302 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_302 :
    recurrence5Scalar1Second.coeff 302 =
      (((((391145041378820748490564544177292742873368549004521644714921264 * 10 ^ 70 +
        7744296825276912046085700530364738202496155482537663966882481735925135) * 10 ^ 70 +
        5025407728623559254695805805589801406232341726660163335633888867770896) * 10 ^ 70 +
        7785538501957881712518708455980760748499714253562333230554175068831643) * 10 ^ 70 +
        2107866229112566083427633589155698443531340029835263501033354447679907) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 0 +
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
    rw [show 175 = 22 +
      153 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (303 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_303 :
    recurrence5Scalar1Second.coeff 303 =
      -(((((149092954542559099523334491660674828814509061414192667933366786 * 10 ^ 70 +
        3586309465633844449431877377347505346510313871966724434870645203940022) * 10 ^ 70 +
        1921766250273008097841680615738824525830483064844826338863628009900399) * 10 ^ 70 +
        9802894780293665164331727206218006024207526611677610655452056806743062) * 10 ^ 70 +
        2363881677007112484988290561756479653340578127981441673187076765409215) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 0 +
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
    rw [show 176 = 22 +
      154 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (304 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_304 :
    recurrence5Scalar1Second.coeff 304 =
      (((((41897576638335387381854275679728096847648649255560023549199204 * 10 ^ 70 +
        1473995811375497234344639982968138082750448109123786416030563660330333) * 10 ^ 70 +
        8179369970035946810305821899753130942261658123435814204339285198326897) * 10 ^ 70 +
        0135891888172957057157733693062530441587021332015737286077809996617167) * 10 ^ 70 +
        3388512998084319718103437104259119497474864789318920744912360660293200) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 0 +
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
    rw [show 177 = 22 +
      155 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (305 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_305 :
    recurrence5Scalar1Second.coeff 305 =
      -(((((1458180846955508461862963702514714559970127299720386113838348 * 10 ^ 70 +
        6334480208531708773622340103854972232981278460471433544821050600158426) * 10 ^ 70 +
        9625440824824733845322184939722412489147408186890315420730207468033025) * 10 ^ 70 +
        6850530669047813422965464876423773967654785092784237650628331948977606) * 10 ^ 70 +
        5771676677098836628740973532263807995193320977366909949828578559256322) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 0 +
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
    rw [show 178 = 22 +
      156 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (306 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_306 :
    recurrence5Scalar1Second.coeff 306 =
      -(((((9723604403445129348559796539204214200204517905723768738460266 * 10 ^ 70 +
        1509490978831947357663738065134275135285208628489722245658167199209967) * 10 ^ 70 +
        4814872411700730127904441969974442512821996942609312216138156662196063) * 10 ^ 70 +
        4323507478804117699418804635538885114462299226399961564120118322922932) * 10 ^ 70 +
        1706353694549363364768238423254780424769358187252073007237494922264556) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 0 +
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
    rw [show 179 = 22 +
      157 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (307 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_307 :
    recurrence5Scalar1Second.coeff 307 =
      (((((10004198687386805531903383372993001192116101692876815153405843 * 10 ^ 70 +
        9161849720204603468279743352450711784919234666096924099405825434773207) * 10 ^ 70 +
        1048208895615955653098247491789797938932603804843595949056314636282686) * 10 ^ 70 +
        1123311795634236942231635448202224113599663102564850223150136064195646) * 10 ^ 70 +
        1005680813196056344002626024849063313943331696488986290244141972718162) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 308 = 0 +
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
    rw [show 180 = 22 +
      158 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (308 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_308 :
    recurrence5Scalar1Second.coeff 308 =
      -(((((7336279763593442653225803126631471834231262722233553400611321 * 10 ^ 70 +
        1812587764243142864777470617016623011219644120318412983582202525637027) * 10 ^ 70 +
        5858762562499903335679158075946135177010902392553766401371853036145414) * 10 ^ 70 +
        9309186997772139243739646845916997569959590439876696772561404456826718) * 10 ^ 70 +
        8634962530270923705578447524720769911897230597775160904400326857207386) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 309 = 0 +
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
    rw [show 181 = 22 +
      159 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (309 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_309 :
    recurrence5Scalar1Second.coeff 309 =
      (((((4639964971166015012113874495662281402943717557921462154161557 * 10 ^ 70 +
        8977137953584330441133886852659725207721780226136541878029443626619987) * 10 ^ 70 +
        4420288345283149354329383721209323385121985710305612865182793919895330) * 10 ^ 70 +
        1472128701026508543404190799532979173430137424441021661016971973400039) * 10 ^ 70 +
        2762866398873521460927813415551663305831075705407071468986116141775097) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 310 = 0 +
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
    rw [show 182 = 22 +
      160 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (310 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_310 :
    recurrence5Scalar1Second.coeff 310 =
      -(((((2682823207291678466670927146843562943026179900401971011529017 * 10 ^ 70 +
        5416191132403294029766563757278568556566073910535941498671545092458850) * 10 ^ 70 +
        8172445184650187056969066709439931186504700269293363580106192875816270) * 10 ^ 70 +
        4411382598394492673488076448024278367288808149891799713214394909156639) * 10 ^ 70 +
        2072192530295361796013156044993046401116309603458277301239357752616751) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 0 +
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
    rw [show 183 = 22 +
      161 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (311 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_311 :
    recurrence5Scalar1Second.coeff 311 =
      (((((1455361287534448561249940169647796478118388535920184894931645 * 10 ^ 70 +
        1716312565262863482279086997161580721247215006865288568368519514971536) * 10 ^ 70 +
        3927444320342226131547417105866107006496117548038259668562993802886738) * 10 ^ 70 +
        0249283929351268584969481507212723530552106149744864057704850048819495) * 10 ^ 70 +
        5688611232918874114230000944655977977385727684175080211110444120289086) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 0 +
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
    rw [show 184 = 22 +
      162 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (312 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_312 :
    recurrence5Scalar1Second.coeff 312 =
      -(((((751087093815120576182514881101139471639755581270806031857205 * 10 ^ 70 +
        9248296708214817074425945946576471573074767871228254774729746617094647) * 10 ^ 70 +
        3684436626699412454082660962402288739668068974660108565080928233800430) * 10 ^ 70 +
        2461916168120322619303221173405694686675829769470938791260634147685025) * 10 ^ 70 +
        8254804852217539715604084418425725084062831165792447483956360297726671) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 0 +
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
    rw [show 185 = 22 +
      163 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (313 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_313 :
    recurrence5Scalar1Second.coeff 313 =
      (((((371834719738054444094502886692588216050571107502938195010843 * 10 ^ 70 +
        3835040054944701274539126390631053351721154953289689319189057338925077) * 10 ^ 70 +
        6672469764519947497062810896670906580790123312864855682568367198916030) * 10 ^ 70 +
        7960061838914315616896508135943415438074584220394718553504475825442136) * 10 ^ 70 +
        6216649162656010769908561383097006756322451340852174820275114878072244) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 0 +
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
    rw [show 186 = 22 +
      164 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (314 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_314 :
    recurrence5Scalar1Second.coeff 314 =
      -(((((177507602910461013637224763724988037637233669981703304399881 * 10 ^ 70 +
        7319938681601143041318316195702810385766665879884599326872802339879167) * 10 ^ 70 +
        4695122184111924141993357239079880744411769693823872574078281300927820) * 10 ^ 70 +
        6255410805532866430465823256050427036213699994295935274784556037507897) * 10 ^ 70 +
        6234220833146489178072601543191649017131514171563001604291783465294868) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
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
    rw [show 186 = 21 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (315 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_315 :
    recurrence5Scalar1Second.coeff 315 =
      (((((81984773373159359630707702317499426127859248433625150965062 * 10 ^ 70 +
        0558216272346159698749341018288284757318536944724633583092550614675564) * 10 ^ 70 +
        6699666339290067658917426042034355339444184387671003449542724507147637) * 10 ^ 70 +
        8839464487938377363826236550952141039026471198937698297669052135689300) * 10 ^ 70 +
        6544523912380558559443070074512337711626909674355894478456574303375652) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 2 +
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
    rw [show 186 = 20 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (316 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_316 :
    recurrence5Scalar1Second.coeff 316 =
      -(((((36708586584393915271825808620380502367107978649706848455316 * 10 ^ 70 +
        1265362642352816977990748756115640925423105164004158432540504683888093) * 10 ^ 70 +
        8082686479320100446630601633971980464476033265985428919964933596751827) * 10 ^ 70 +
        4522457304957968357904507153296103825338612044817052332392580588319814) * 10 ^ 70 +
        4242379799310427643861331054446953319444977889125003608379272999831384) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 3 +
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
    rw [show 186 = 19 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (317 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_317 :
    recurrence5Scalar1Second.coeff 317 =
      (((((15949488319001086746067107223350996962628542249589361957748 * 10 ^ 70 +
        4588414723283039812189081176727793031037283000227354419115050616821477) * 10 ^ 70 +
        8381037600503636717754673503097418313453946223746702742204052284083730) * 10 ^ 70 +
        0293821439950232774525954612102668809245315732945491881512985657257405) * 10 ^ 70 +
        6658278276157499338020783822105063399646221205575268084556324426930968) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 4 +
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
    rw [show 186 = 18 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (318 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_318 :
    recurrence5Scalar1Second.coeff 318 =
      -(((((6725388598180566579070652854606044984060843451971034555456 * 10 ^ 70 +
        2436869464098807226635782097042827108807855993180589291075569768025871) * 10 ^ 70 +
        3783913092475798704824865492072340193269024512390861227171819971810476) * 10 ^ 70 +
        6301222487246808775494029389483307490235100500595193706264622156925606) * 10 ^ 70 +
        6414666612112388322332386845007263049307980482185036604236203970247011) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 5 +
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
    rw [show 186 = 17 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (319 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_319 :
    recurrence5Scalar1Second.coeff 319 =
      (((((2750203127528861247934827898385430120446721454530324238733 * 10 ^ 70 +
        5771627232336358332134584354232831353161649632326631145415000663005372) * 10 ^ 70 +
        4465770284058463109286184076051107738358093542802183889425926597788737) * 10 ^ 70 +
        7059031956316939471074659475808843774305782608333065863635166577567196) * 10 ^ 70 +
        0004692461114695525963533338345949505434106781332891887625624477616605) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 6 +
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
    rw [show 186 = 16 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (320 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_320 :
    recurrence5Scalar1Second.coeff 320 =
      -(((((1088900000501486070304411951160644874878116852013645714258 * 10 ^ 70 +
        0762598206768866447954309957348173747229286388343734761549928088604539) * 10 ^ 70 +
        1550238279381474588325510609351849187834543406946511697517440599009166) * 10 ^ 70 +
        8157559547736819268892751128490603499568282106075833161252807073182516) * 10 ^ 70 +
        8651001053705641173530492642382152760888524576302131154008101338588434) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 7 +
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
    rw [show 186 = 15 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (321 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_321 :
    recurrence5Scalar1Second.coeff 321 =
      (((((416312306207089145211688256445271782946561170969725031859 * 10 ^ 70 +
        6959684250739117688956435991114784448895975248928989212703963899826862) * 10 ^ 70 +
        1924964945700986214686426044844115891247001013616346152542947843388498) * 10 ^ 70 +
        7033740069828252222402936197046403898855995964848920326428898307333727) * 10 ^ 70 +
        0594704526839482031568353767610018440621954652280549840576594626973778) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 8 +
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
    rw [show 186 = 14 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (322 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_322 :
    recurrence5Scalar1Second.coeff 322 =
      -(((((153054841661330134813535394679392618328113375580062251839 * 10 ^ 70 +
        4373069189388828934173484640169492106143446519198957307768803760621982) * 10 ^ 70 +
        2892390283795357182699165381262347379356491949919858357793173226705577) * 10 ^ 70 +
        8387642207423861011353288619068697905283494432000885960275736890088343) * 10 ^ 70 +
        6117765015910464615372454134592896075463685776054920353304599032186528) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 9 +
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
    rw [show 186 = 13 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (323 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_323 :
    recurrence5Scalar1Second.coeff 323 =
      (((((53758709389451455276748321217364881520828664616024584891 * 10 ^ 70 +
        2705831840540353460594388705718743627181322002882041707530287729001893) * 10 ^ 70 +
        4594127682012560227220880938962871177996827293287966841282882307827705) * 10 ^ 70 +
        3517710408288316120211938326238317576340360538779477077524902872119627) * 10 ^ 70 +
        3802630356969652083630893208994631579294035465877817849612048591724174) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 10 +
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
    rw [show 186 = 12 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (324 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_324 :
    recurrence5Scalar1Second.coeff 324 =
      -(((((17848121292177343208672838772466027451845748273154659950 * 10 ^ 70 +
        8506756300437992487683319509861512256570317415592816757503430360641551) * 10 ^ 70 +
        6270359437080820459320205584420550520929325817798658957038208532273224) * 10 ^ 70 +
        4001833878970443388659647319045355487696185660807487296855522102377495) * 10 ^ 70 +
        7158875250547590459638346885558842665396882202097984803753600373755716) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 11 +
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
    rw [show 186 = 11 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (325 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_325 :
    recurrence5Scalar1Second.coeff 325 =
      (((((5494263070768968859006623384828314199564831227244713402 * 10 ^ 70 +
        2949654569765502573525179346879861078055508078916475982638121942441118) * 10 ^ 70 +
        0498899352185584956231338225170670092964317115319911794091691407594258) * 10 ^ 70 +
        8098983089856391282214674782027426848800424761485566860677775648139233) * 10 ^ 70 +
        6513781730676131960403975179098819593722110868978680507202239555181655) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 12 +
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
    rw [show 186 = 10 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (326 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_326 :
    recurrence5Scalar1Second.coeff 326 =
      -(((((1505571554160591367493920475053265348868448398220830693 * 10 ^ 70 +
        5087889756400908502109937949429410160686500558902726207247643631923390) * 10 ^ 70 +
        9638631821599033450285073520623829683651782726679728691818401104014089) * 10 ^ 70 +
        3204801767399537169117095499029626514585960309985190445444233826424891) * 10 ^ 70 +
        5476046233900889547622676339470348654543635052844261861492574466184932) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 13 +
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
    rw [show 186 = 9 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (327 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_327 :
    recurrence5Scalar1Second.coeff 327 =
      (((((327516982504030173552587967116212527413060418755711797 * 10 ^ 70 +
        3338574089468287695996826863424824267267450088604513462252142158487994) * 10 ^ 70 +
        4147656411634880837412309006339267929242533207366262799341809163352403) * 10 ^ 70 +
        9625351966189714070957047403609957072591819333434403565410901435513424) * 10 ^ 70 +
        1964159484952507170125508715559630949157855124663676439678215981041394) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 14 +
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
    rw [show 186 = 8 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (328 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_328 :
    recurrence5Scalar1Second.coeff 328 =
      -(((((27646967760087116145390054605607495358212899851712060 * 10 ^ 70 +
        2059751239202216454815772662800343748091022579536553165691792391557187) * 10 ^ 70 +
        4778965747338864590179193595168452143944827772864601123598241074266795) * 10 ^ 70 +
        7358085516990910945664890649246849765144461574502103266334909721401153) * 10 ^ 70 +
        4625364414457159055831618251438656190210512551015738036390501098431386) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 15 +
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
    rw [show 186 = 7 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (329 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_329 :
    recurrence5Scalar1Second.coeff 329 =
      -(((((25916699635544732248801953050603069415530300815673858 * 10 ^ 70 +
        1872142744779414415241074207055014667747353880921129029052646732636319) * 10 ^ 70 +
        0755813598577956214660502886580057330898553708926666361998836089227109) * 10 ^ 70 +
        4475251235132167281633112721386109992656984953655669402441973612523113) * 10 ^ 70 +
        5488344709534422207591880985718849145302852891437832317307082559194900) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 330 = 16 +
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
    rw [show 186 = 6 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (330 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_330 :
    recurrence5Scalar1Second.coeff 330 =
      (((((22972729033562199436671074680158377329426355898657826 * 10 ^ 70 +
        1628979571894024677733366705654024221855981595807509666614626386101098) * 10 ^ 70 +
        4098724761689429606592988816047131423636133963214904473623836013529793) * 10 ^ 70 +
        9803882449475159251799734562228869277985655786018640696086397897299443) * 10 ^ 70 +
        4128585027743002723763012814399349833626006109911473040374035487681804) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 331 = 17 +
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
    rw [show 186 = 5 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (331 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_331 :
    recurrence5Scalar1Second.coeff 331 =
      -(((((13296036062477631952671158061407299105239202299006503 * 10 ^ 70 +
        1339788225127190106685395092958828225516187776211937815853204254253009) * 10 ^ 70 +
        0435771328164312164469174102880255207670152541904349469261031176585403) * 10 ^ 70 +
        4179528129304302336546682260538689344290229680607067855945007774855914) * 10 ^ 70 +
        1411686713135647120354759002790863886580813010571332402335800853668066) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 18 +
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
    rw [show 186 = 4 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (332 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_332 :
    recurrence5Scalar1Second.coeff 332 =
      (((((6602150596631818407269041897399009679289274863152224 * 10 ^ 70 +
        5891857188228177152372479821434509261443089466150627475289565823858362) * 10 ^ 70 +
        3433718691687042638565587862783810602409812011247219707555874736224463) * 10 ^ 70 +
        3694668462452937983346979187845432282169332090614724024214224298430756) * 10 ^ 70 +
        0418166451091328889451348131474903646728013157842624469852188478884019) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 19 +
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
    rw [show 186 = 3 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (333 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_333 :
    recurrence5Scalar1Second.coeff 333 =
      -(((((3028142953401653330234505335733666491471209195500936 * 10 ^ 70 +
        8568092471288498628114681953366454772406938797366731048662113702771931) * 10 ^ 70 +
        3661371020014994612293365331764823723106660749260730495444926643486870) * 10 ^ 70 +
        3842101376768259411981054500431035985981627325624295387070640067014987) * 10 ^ 70 +
        0528342779370547850073261899788819320875211156076531774490999767155350) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 20 +
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
    rw [show 186 = 2 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (334 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_334 :
    recurrence5Scalar1Second.coeff 334 =
      (((((1324804971982629346927573974915605508498522664878683 * 10 ^ 70 +
        1758429417627581466061929863369146798399981900804159783601550545892801) * 10 ^ 70 +
        4397796099621108613116766282388197125046810332965062646268577115282078) * 10 ^ 70 +
        8958783659342848804636931103700876707854971527145626213774253642106814) * 10 ^ 70 +
        5291505268827630689668339538931286574632043399323195732252603451707156) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 21 +
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
    rw [show 186 = 1 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (335 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_335 :
    recurrence5Scalar1Second.coeff 335 =
      -(((((562358636115556575648827387778285915231530328612444 * 10 ^ 70 +
        9782926018583052534156190096777046889683715962870330888926401030833264) * 10 ^ 70 +
        3838476269317402553372214306217006062836972676416562568645426743986872) * 10 ^ 70 +
        7840811744304902392343779859111132107152994644342412325199520329574126) * 10 ^ 70 +
        4161460169827091515488081783235126501831890113629980261325336023884972) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 22 +
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
  rw [recurrence5Scalar1Second_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (336 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_336 :
    recurrence5Scalar1Second.coeff 336 =
      (((((233821476619915351287719971031453447436881297864855 * 10 ^ 70 +
        5892809704236996860710724292756064068393008800632043120600582489656925) * 10 ^ 70 +
        9391301992198802285293181945981798873117861831986622064852651257267665) * 10 ^ 70 +
        7026677443207661426588399966677103599061525017834025935431469088996329) * 10 ^ 70 +
        0924818141655611076945270205059583372454066838857987123103959127962584) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 23 +
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
    rw [show 218 = 31 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (337 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_337 :
    recurrence5Scalar1Second.coeff 337 =
      -(((((95685220416366701224991670523065027753388680144316 * 10 ^ 70 +
        8678621836812182541478551377629219564960759985410247997880333239374885) * 10 ^ 70 +
        4197745600059924079361060268591268754825172016121608920332530052054247) * 10 ^ 70 +
        3337117072717385915525035336996815187820203465783831721172498912226768) * 10 ^ 70 +
        3668579989167954566801165223432256268112531324273471720448589209008783) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 24 +
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
    rw [show 218 = 30 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (338 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_338 :
    recurrence5Scalar1Second.coeff 338 =
      (((((38598546701800529991774694965596449275972407378944 * 10 ^ 70 +
        8326145887228343204439783964492693654629666587135877412564907932161772) * 10 ^ 70 +
        5336972106367828148346541471418029767609003913841604616737907974692038) * 10 ^ 70 +
        5266627040521565591513010463109432724976795316726093416241439369738970) * 10 ^ 70 +
        7155425551317541813655288979831830818977694826678934338932965649816186) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 25 +
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
    rw [show 218 = 29 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (339 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_339 :
    recurrence5Scalar1Second.coeff 339 =
      -(((((15339100553447471413713988993413984171407740605548 * 10 ^ 70 +
        6932848794296020502792178059927767380127063391999673619668456510368885) * 10 ^ 70 +
        5536867433420274677481897234641725089789020196640385560010222499946964) * 10 ^ 70 +
        1296211234003044281980560186231628070979251078314700443813737835669853) * 10 ^ 70 +
        6553821125423267466469375499648004125328413713353737457295805893091477) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 26 +
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
    rw [show 218 = 28 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (340 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_340 :
    recurrence5Scalar1Second.coeff 340 =
      (((((5994004594942406626260159694580470861160071010187 * 10 ^ 70 +
        6903873569581314615729225622283245203259848939593893273875779356909950) * 10 ^ 70 +
        2158527094044550287898649995044012230249358485847538864634280888320570) * 10 ^ 70 +
        4656523035095172775002684999419682532392774037860596550667297407942888) * 10 ^ 70 +
        9664186414375006485772472621068396177820814767046827143558477936698958) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 27 +
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
    rw [show 218 = 27 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (341 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_341 :
    recurrence5Scalar1Second.coeff 341 =
      -(((((2297535362288852518071321729032267122541796262281 * 10 ^ 70 +
        0816341277380389166288757343103829880693950052139521012543717801563275) * 10 ^ 70 +
        7457574983550834266882332507205651640276120405402438899114086317689622) * 10 ^ 70 +
        4344811500378743570914616185722846940296932477020073306270597609656544) * 10 ^ 70 +
        3284461724550669945139249376032304251352454777340451423549090185009849) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 28 +
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
    rw [show 218 = 26 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (342 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_342 :
    recurrence5Scalar1Second.coeff 342 =
      (((((861666381814727643718985956638270145544438545253 * 10 ^ 70 +
        5724865464560371672574024390585887643218356822582261854420594525639454) * 10 ^ 70 +
        7695415641361030177982053695173882563694556393436488564038972890833851) * 10 ^ 70 +
        3881965371984118973678012855386686659768089337678370043157847161884828) * 10 ^ 70 +
        2740980225134179008437724753176250517038981480321588311774371708762469) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 29 +
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
    rw [show 218 = 25 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (343 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_343 :
    recurrence5Scalar1Second.coeff 343 =
      -(((((315450555584257392077962914709188339354209140962 * 10 ^ 70 +
        0646328894100113640810748998421943871309571080135831494127160029051442) * 10 ^ 70 +
        2898729034626967118552948067469125158310558415333311835093687953610787) * 10 ^ 70 +
        4401797000155599854334623230551722141172741760256211283781146632290821) * 10 ^ 70 +
        7256371225541648112435857975333906693530813641461626355193228776728896) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 30 +
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
    rw [show 218 = 24 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (344 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_344 :
    recurrence5Scalar1Second.coeff 344 =
      (((((112496589297190994962785861627477343694750686674 * 10 ^ 70 +
        5238708696782363671227562021879262045874748399572293621573906714726303) * 10 ^ 70 +
        3922522198903615137810788059914840250739196334755968350530623769907711) * 10 ^ 70 +
        0175838328289109669983550140999905923175139344452978663485048385034283) * 10 ^ 70 +
        7333376587529453950453175172380634859489962188024889335321810639714810) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 31 +
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
    rw [show 218 = 23 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (345 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_345 :
    recurrence5Scalar1Second.coeff 345 =
      -(((((39008653564691029276429678370698865240436553617 * 10 ^ 70 +
        6223900746113779783381273188162747296794197750966147853459368708471569) * 10 ^ 70 +
        8595643902147333736686589526892528783653283922121569549886401581630794) * 10 ^ 70 +
        7045141658896132306794767422446261738069576118385568873422058127282382) * 10 ^ 70 +
        3779817843155136021603114684303740094010599235369027396470814579766339) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 32 +
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
    rw [show 218 = 22 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (346 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_346 :
    recurrence5Scalar1Second.coeff 346 =
      (((((13128777835287869973950812965318570192428603548 * 10 ^ 70 +
        6527852846643477452647841465684084300539183048936210594854726952093175) * 10 ^ 70 +
        5392927111724688076737959554452585670967881377723639568724036879692736) * 10 ^ 70 +
        8276918433205224354548398173333585406595628690102377130267827391768191) * 10 ^ 70 +
        3701253667344892609607051084138061779356489349823803858642104665470442) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 33 +
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
    rw [show 218 = 21 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (347 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_347 :
    recurrence5Scalar1Second.coeff 347 =
      -(((((4280304917557224883625245039847239376832133064 * 10 ^ 70 +
        3242635127835624061196940237734579528490779716022662296080045060762437) * 10 ^ 70 +
        9748808303884367642966724307368886154236369307271442825987592584928845) * 10 ^ 70 +
        1545499532999525382393736812066053598094650282140083054180911225244896) * 10 ^ 70 +
        3259545820586753039049293979449016891078651271336462410819498246011492) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 34 +
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
    rw [show 218 = 20 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (348 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_348 :
    recurrence5Scalar1Second.coeff 348 =
      (((((1348322452596628755843421259012578543233511401 * 10 ^ 70 +
        4164828275579021262131646675279477073039870867028640689038789783172033) * 10 ^ 70 +
        3518591278203242467729012678102634340494715546789647655205892101978135) * 10 ^ 70 +
        3802558940180836950305107322272176845048890639456722491694106410568677) * 10 ^ 70 +
        2923720653554723214382426112965170670857580825135411294461686172701288) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 35 +
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
    rw [show 218 = 19 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (349 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_349 :
    recurrence5Scalar1Second.coeff 349 =
      -(((((408786387118651441798083911124788925835947724 * 10 ^ 70 +
        0258356952154950338127116775017560432219153042853184284445690493905951) * 10 ^ 70 +
        8064953251975894647948639549069943693441643114290437911039110851021687) * 10 ^ 70 +
        2122262385529372837757046562164461539798618886711666003098073193113533) * 10 ^ 70 +
        9442101305797844029874849948176197220721214594739710478217391144970574) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 36 +
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
    rw [show 218 = 18 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (350 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_350 :
    recurrence5Scalar1Second.coeff 350 =
      (((((118515391371276174528484356851923215860145813 * 10 ^ 70 +
        7588289332250952422300665778348389583084210353572275619232775740009473) * 10 ^ 70 +
        6670374484038202055034656007715366201488020802504191404729926369888330) * 10 ^ 70 +
        2111043859253232174847481954819174700851665262260820883293419588083680) * 10 ^ 70 +
        7425458248620476302808025101691911982395208267478008004980669202709758) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 37 +
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
    rw [show 218 = 17 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (351 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_351 :
    recurrence5Scalar1Second.coeff 351 =
      -(((((32474488626337064840603043663624737289442078 * 10 ^ 70 +
        9905672466321288244302215572199835677658595595028821230668364470288260) * 10 ^ 70 +
        7613054872555283823123774993845657983138183672130624271355501242726500) * 10 ^ 70 +
        6125817005482812258955418543483367041663098481501759670710660687931093) * 10 ^ 70 +
        7809760072845087962163297721431167987925665562684285993362915474109467) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 38 +
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
    rw [show 218 = 16 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (352 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_352 :
    recurrence5Scalar1Second.coeff 352 =
      (((((8214856301973562641133081194341484599043814 * 10 ^ 70 +
        5018740841487850281529327888666879801024765912871616331377828024137334) * 10 ^ 70 +
        0782869478581655218018154543153309839115807296413123164782628071738666) * 10 ^ 70 +
        4355733526535108516357542526798239143552735543218232251956017791883249) * 10 ^ 70 +
        6904027767988467876853859148389859890485603092641135862978772426861844) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 39 +
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
    rw [show 218 = 15 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (353 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_353 :
    recurrence5Scalar1Second.coeff 353 =
      -(((((1814415954992877196230134710294454887056422 * 10 ^ 70 +
        5843983828126537247411676938695118834289432179546764831719694537666344) * 10 ^ 70 +
        3054174069581730022310142067632724826673904570381597094992037997861692) * 10 ^ 70 +
        0513983335055887612178005715215748420381770710980523033646590705848707) * 10 ^ 70 +
        1851084785067237724052507021675291123484578103197281498471135115958716) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 40 +
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
    rw [show 218 = 14 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (354 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_354 :
    recurrence5Scalar1Second.coeff 354 =
      (((((289518783375197744798711489600493494339348 * 10 ^ 70 +
        5799460065630929869577079238837185413059350762738568104419479272251043) * 10 ^ 70 +
        1133049581935441782719329804003160689803544175555651950083185310249486) * 10 ^ 70 +
        9319429118229118847270860351374560680885745964816725794250864854204814) * 10 ^ 70 +
        3884863427566483169401116119601279980363575764208437153531994144818578) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 41 +
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
    rw [show 218 = 13 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (355 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_355 :
    recurrence5Scalar1Second.coeff 355 =
      (((((8040382213582646232664492285334762491957 * 10 ^ 70 +
        8509592775026325224482995592101454321587249497894343136362252330249554) * 10 ^ 70 +
        8676710283494543297976606455435850706698866940150942533144724648720872) * 10 ^ 70 +
        3642736792333372688169705892053755170045078071209316458581694156838381) * 10 ^ 70 +
        9495130458602455893482647650297043372866772461092606026012448993577583) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 42 +
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
    rw [show 218 = 12 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (356 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_356 :
    recurrence5Scalar1Second.coeff 356 =
      -(((((36573005340503056405355762423486460800205 * 10 ^ 70 +
        6007523207334026424005957829854204994994773799319160905603646813055826) * 10 ^ 70 +
        9023486149503533383768904525538629117053282699530734403020886288577757) * 10 ^ 70 +
        2194824897690699954612122527383894780258646578516259869238509436304945) * 10 ^ 70 +
        2815046643319021775714281000375037187322002229639063311373700260829420) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 357 = 43 +
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
    rw [show 218 = 11 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (357 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_357 :
    recurrence5Scalar1Second.coeff 357 =
      (((((22992984451012360920566862582528372816640 * 10 ^ 70 +
        0304325849944314250742214484037400500282689947189756840315535802650481) * 10 ^ 70 +
        3203877253966780493080428692512505793587463507170145535568737384896523) * 10 ^ 70 +
        9836378727203913815916216671915590231469214686728779523494360443525118) * 10 ^ 70 +
        7415019278334048831473647487067053713485928403959380376280947243562076) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 358 = 44 +
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
    rw [show 218 = 10 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (358 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_358 :
    recurrence5Scalar1Second.coeff 358 =
      -(((((11067390736272118585116897122399683735437 * 10 ^ 70 +
        8039198124405148051660271936440514438650690100866996731133841139619477) * 10 ^ 70 +
        7190623453618874546194288652975196626842420523914553778991265360773471) * 10 ^ 70 +
        9052256664182849252705665237993210658195935830801005573456370287589222) * 10 ^ 70 +
        6870996416525542624496189314030992913990985891924843304297924420383131) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 359 = 45 +
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
    rw [show 218 = 9 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (359 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_359 :
    recurrence5Scalar1Second.coeff 359 =
      (((((4754677196634719580117076541896676463972 * 10 ^ 70 +
        9615997843017971092457495554298890174766883819434126293876837640828311) * 10 ^ 70 +
        9463450789229764779951529954045623216182691474436523156177244469257462) * 10 ^ 70 +
        4328471841082515586210748843910950070745549522650423370392893769117384) * 10 ^ 70 +
        3096622329913450659846378727407640881302774325671837414990311064830799) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 360 = 46 +
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
    rw [show 218 = 8 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (360 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_360 :
    recurrence5Scalar1Second.coeff 360 =
      -(((((1918034418750913008559714735448148902747 * 10 ^ 70 +
        2430312383117438339448791253865641949809912525011141307736240204884238) * 10 ^ 70 +
        7968593756145547658691487638807021286114435429405401769767011940038194) * 10 ^ 70 +
        8045416884116725442127123131513950427357496836055643856399612762241331) * 10 ^ 70 +
        9605962006582523353323545315617469383152630115251191838309618876490884) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 361 = 47 +
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
    rw [show 218 = 7 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (361 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_361 :
    recurrence5Scalar1Second.coeff 361 =
      (((((743571214065932957879963002972892914823 * 10 ^ 70 +
        1123127084017139660210525555503231812704107353498510093789113125804790) * 10 ^ 70 +
        0934327388946352068175257788187457937775258376434498379224458764295908) * 10 ^ 70 +
        1379308955277900017781312478272942794107281442917957722919227702071820) * 10 ^ 70 +
        2417259033626471007357220287838821410274360303213500455811004819466595) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 362 = 48 +
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
    rw [show 218 = 6 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (362 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_362 :
    recurrence5Scalar1Second.coeff 362 =
      -(((((280404857859510269664607428316209502767 * 10 ^ 70 +
        4137777957654490186917115926540252821700286480302686282252969703511124) * 10 ^ 70 +
        8190569605806353999732623730415307360238410297625772725816029449441994) * 10 ^ 70 +
        5641007298847477855997699048951316965063013659219201732635419014205139) * 10 ^ 70 +
        2427408118282059769372560707374573187390356313323975835797673439383422) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 49 +
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
    rw [show 218 = 5 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1Second_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (363 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_363 :
    recurrence5Scalar1Second.coeff 363 =
      (((((103521311683637949159095389345320710835 * 10 ^ 70 +
        8621840190883803575659477223297840025068112626398924411348498622583971) * 10 ^ 70 +
        3461628019145284174092437875080617354596670117197609014746985696327013) * 10 ^ 70 +
        3783831104005256737806215224924229612815844006769317094694184943511131) * 10 ^ 70 +
        6689909288927976498322982429603451784271451160281250321368531429199951) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 364 = 50 +
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
    rw [show 218 = 4 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
