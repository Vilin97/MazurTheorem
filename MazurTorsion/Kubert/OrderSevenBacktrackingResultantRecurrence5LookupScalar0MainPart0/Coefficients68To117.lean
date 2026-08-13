/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0MainPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
