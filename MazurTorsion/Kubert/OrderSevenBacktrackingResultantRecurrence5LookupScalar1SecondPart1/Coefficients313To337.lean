/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1SecondPart1Simp
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
