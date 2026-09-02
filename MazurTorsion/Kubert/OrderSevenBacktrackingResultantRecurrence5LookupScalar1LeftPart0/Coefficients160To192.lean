/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5LeadingSquare_coeff_0
  recurrence5LeadingSquare_coeff_1
  recurrence5LeadingSquare_coeff_2
  recurrence5LeadingSquare_coeff_3
  recurrence5LeadingSquare_coeff_4
  recurrence5LeadingSquare_coeff_5
  recurrence5LeadingSquare_coeff_6
  recurrence5LeadingSquare_coeff_7
  recurrence5LeadingSquare_coeff_8
  recurrence5LeadingSquare_coeff_9
  recurrence5LeadingSquare_coeff_10
  recurrence5LeadingSquare_coeff_11
  recurrence5LeadingSquare_coeff_12
  recurrence5LeadingSquare_coeff_13
  recurrence5LeadingSquare_coeff_14
  recurrence5LeadingSquare_coeff_15
  recurrence5LeadingSquare_coeff_16
  recurrence5LeadingSquare_coeff_17
  recurrence5LeadingSquare_coeff_18
  recurrence5LeadingSquare_coeff_19
  recurrence5LeadingSquare_coeff_20
  recurrence5LeadingSquare_coeff_21
  recurrence5LeadingSquare_coeff_22
  recurrence5LeadingSquare_coeff_23
  recurrence5LeadingSquare_coeff_24
  recurrence5LeadingSquare_coeff_25
  recurrence5LeadingSquare_coeff_26
  recurrence5LeadingSquare_coeff_27
  recurrence5LeadingSquare_coeff_28
  recurrence5LeadingSquare_coeff_29
  recurrence5LeadingSquare_coeff_30
  recurrence5LeadingSquare_coeff_31
  recurrence5LeadingSquare_coeff_32
  recurrence5LeadingSquare_coeff_33
  recurrence5LeadingSquare_coeff_34
  recurrence5LeadingSquare_coeff_35
  recurrence5LeadingSquare_coeff_36
  recurrence5LeadingSquare_coeff_37
  recurrence5LeadingSquare_coeff_38
  recurrence5LeadingSquare_coeff_39
  recurrence5LeadingSquare_coeff_40
  recurrence5LeadingSquare_coeff_41
  recurrence5LeadingSquare_coeff_42
  recurrence5LeadingSquare_coeff_43
  recurrence5LeadingSquare_coeff_44
  recurrence5LeadingSquare_coeff_45
  recurrence5LeadingSquare_coeff_46
  recurrence5LeadingSquare_coeff_47
  recurrence5LeadingSquare_coeff_48
  recurrence5LeadingSquare_coeff_49
  recurrence5LeadingSquare_coeff_50
  recurrence5LeadingSquare_coeff_51
  recurrence5LeadingSquare_coeff_52
  recurrence5LeadingSquare_coeff_53
  recurrence5LeadingSquare_coeff_54
  recurrence5LeadingSquare_coeff_55
  recurrence5LeadingSquare_coeff_56
  recurrence5LeadingSquare_coeff_57
  recurrence5LeadingSquare_coeff_58
  recurrence5LeadingSquare_coeff_59
  recurrence5LeadingSquare_coeff_60
  recurrence5LeadingSquare_coeff_61
  recurrence5LeadingSquare_coeff_62
  recurrence5LeadingSquare_coeff_63

attribute [local simp]
  recurrence5LeadingSquare_coeff_64
  recurrence5LeadingSquare_coeff_65
  recurrence5LeadingSquare_coeff_66
  recurrence5LeadingSquare_coeff_67
  recurrence5LeadingSquare_coeff_68
  recurrence5LeadingSquare_coeff_69
  recurrence5LeadingSquare_coeff_70
  recurrence5LeadingSquare_coeff_71
  recurrence5LeadingSquare_coeff_72
  recurrence5LeadingSquare_coeff_73
  recurrence5LeadingSquare_coeff_74
  recurrence5LeadingSquare_coeff_75
  recurrence5LeadingSquare_coeff_76
  recurrence5LeadingSquare_coeff_77
  recurrence5LeadingSquare_coeff_78
  recurrence5LeadingSquare_coeff_79
  recurrence5LeadingSquare_coeff_80
  recurrence5LeadingSquare_coeff_81
  recurrence5LeadingSquare_coeff_82
  recurrence5LeadingSquare_coeff_83
  recurrence5LeadingSquare_coeff_84
  recurrence5LeadingSquare_coeff_85
  recurrence5LeadingSquare_coeff_86
  recurrence5LeadingSquare_coeff_87
  recurrence5LeadingSquare_coeff_88
  recurrence5LeadingSquare_coeff_89
  recurrence5LeadingSquare_coeff_90
  recurrence5LeadingSquare_coeff_91
  recurrence5LeadingSquare_coeff_92
  recurrence5LeadingSquare_coeff_93
  recurrence5LeadingSquare_coeff_94
  recurrence5LeadingSquare_coeff_95
  recurrence5LeadingSquare_coeff_96
  recurrence5LeadingSquare_coeff_97
  recurrence5LeadingSquare_coeff_98
  recurrence5LeadingSquare_coeff_99
  recurrence5LeadingSquare_coeff_100
  recurrence5LeadingSquare_coeff_101
  recurrence5LeadingSquare_coeff_102
  recurrence5LeadingSquare_coeff_103
  recurrence5LeadingSquare_coeff_104
  recurrence5LeadingSquare_coeff_105
  recurrence5LeadingSquare_coeff_106
  recurrence5LeadingSquare_coeff_107
  recurrence5LeadingSquare_coeff_108
  recurrence5LeadingSquare_coeff_109
  recurrence5LeadingSquare_coeff_110
  recurrence5LeadingSquare_coeff_111
  recurrence5LeadingSquare_coeff_112
  recurrence5LeadingSquare_coeff_113
  recurrence5LeadingSquare_coeff_114
  recurrence5LeadingSquare_coeff_115
  recurrence5LeadingSquare_coeff_116
  recurrence5LeadingSquare_coeff_117
  recurrence5LeadingSquare_coeff_118
  recurrence5LeadingSquare_coeff_119
  recurrence5LeadingSquare_coeff_120
  recurrence5LeadingSquare_coeff_121
  recurrence5LeadingSquare_coeff_122
  recurrence5LeadingSquare_coeff_123
  recurrence5LeadingSquare_coeff_124
  recurrence5LeadingSquare_coeff_125
  recurrence5LeadingSquare_coeff_126
  recurrence5LeadingSquare_coeff_127

attribute [local simp]
  recurrence5LeadingSquare_coeff_128
  recurrence5LeadingSquare_coeff_129
  recurrence5LeadingSquare_coeff_130
  recurrence5LeadingSquare_coeff_131
  recurrence5LeadingSquare_coeff_132
  recurrence5LeadingSquare_coeff_133
  recurrence5LeadingSquare_coeff_134
  recurrence5LeadingSquare_coeff_135
  recurrence5LeadingSquare_coeff_136
  recurrence5LeadingSquare_coeff_137
  recurrence5LeadingSquare_coeff_138
  recurrence5LeadingSquare_coeff_139
  recurrence5LeadingSquare_coeff_140
  recurrence5LeadingSquare_coeff_141
  recurrence5LeadingSquare_coeff_142
  recurrence5LeadingSquare_coeff_143
  recurrence5LeadingSquare_coeff_144
  recurrence5LeadingSquare_coeff_145
  recurrence5LeadingSquare_coeff_146
  recurrence5LeadingSquare_coeff_147
  recurrence5LeadingSquare_coeff_148
  recurrence5LeadingSquare_coeff_149
  recurrence5LeadingSquare_coeff_150
  recurrence5LeadingSquare_coeff_151
  recurrence5LeadingSquare_coeff_152
  recurrence5LeadingSquare_coeff_153
  recurrence5LeadingSquare_coeff_154
  recurrence5LeadingSquare_coeff_155
  recurrence5LeadingSquare_coeff_156
  recurrence5LeadingSquare_coeff_157
  recurrence5LeadingSquare_coeff_158
  recurrence5LeadingSquare_coeff_159
  recurrence5LeadingSquare_coeff_160
  recurrence5LeadingSquare_coeff_161
  recurrence5LeadingSquare_coeff_162
  recurrence5LeadingSquare_coeff_163
  recurrence5LeadingSquare_coeff_164
  recurrence5LeadingSquare_coeff_165
  recurrence5LeadingSquare_coeff_166
  recurrence5LeadingSquare_coeff_167
  recurrence5LeadingSquare_coeff_168
  recurrence5LeadingSquare_coeff_169
  recurrence5LeadingSquare_coeff_170
  recurrence5LeadingSquare_coeff_171
  recurrence5LeadingSquare_coeff_172
  recurrence5LeadingSquare_coeff_173
  recurrence5LeadingSquare_coeff_174
  recurrence5LeadingSquare_coeff_175
  recurrence5LeadingSquare_coeff_176
  recurrence5LeadingSquare_coeff_177
  recurrence5LeadingSquare_coeff_178
  recurrence5LeadingSquare_coeff_179
  recurrence5LeadingSquare_coeff_180
  recurrence5LeadingSquare_coeff_181
  recurrence5LeadingSquare_coeff_182
  recurrence5LeadingSquare_coeff_183
  recurrence5LeadingSquare_coeff_184
  recurrence5LeadingSquare_coeff_185
  recurrence5LeadingSquare_coeff_186
  recurrence5LeadingSquare_coeff_187
  recurrence5LeadingSquare_coeff_188
  recurrence5LeadingSquare_coeff_189
  recurrence5LeadingSquare_coeff_190
  recurrence5LeadingSquare_coeff_191

attribute [local simp]
  recurrence5LeadingSquare_coeff_192
  recurrence5LeadingSquare_coeff_193
  recurrence5LeadingSquare_coeff_194
  recurrence5LeadingSquare_coeff_195
  recurrence5LeadingSquare_coeff_196
  recurrence5LeadingSquare_coeff_197
  recurrence5LeadingSquare_coeff_198
  recurrence5LeadingSquare_coeff_199
  recurrence5LeadingSquare_coeff_200
  recurrence5LeadingSquare_coeff_201
  recurrence5LeadingSquare_coeff_202
  recurrence5LeadingSquare_coeff_203
  recurrence5LeadingSquare_coeff_204
  recurrence5LeadingSquare_coeff_205
  recurrence5LeadingSquare_coeff_206
  recurrence5LeadingSquare_coeff_207
  recurrence5LeadingSquare_coeff_208
  recurrence5LeadingSquare_coeff_209
  recurrence5LeadingSquare_coeff_210
  recurrence5LeadingSquare_coeff_211
  recurrence5LeadingSquare_coeff_212
  recurrence5LeadingSquare_coeff_213
  recurrence5LeadingSquare_coeff_214
  recurrence5LeadingSquare_coeff_215
  recurrence5LeadingSquare_coeff_216
  recurrence5LeadingSquare_coeff_217
  recurrence5LeadingSquare_coeff_218
  recurrence5LeadingSquare_coeff_219
  recurrence5LeadingSquare_coeff_220
  recurrence5LeadingSquare_coeff_221
  recurrence5LeadingSquare_coeff_222
  recurrence5LeadingSquare_coeff_223
  recurrence5LeadingSquare_coeff_224
  recurrence5LeadingSquare_coeff_225
  recurrence5LeadingSquare_coeff_226
  recurrence5LeadingSquare_coeff_227
  recurrence5LeadingSquare_coeff_228
  recurrence5LeadingSquare_coeff_229
  recurrence5LeadingSquare_coeff_230
  recurrence5LeadingSquare_coeff_231
  recurrence5LeadingSquare_coeff_232
  recurrence5LeadingSquare_coeff_233
  recurrence5LeadingSquare_coeff_234
  recurrence5LeadingSquare_coeff_235
  recurrence5LeadingSquare_coeff_236
  recurrence5LeadingSquare_coeff_237
  recurrence5LeadingSquare_coeff_238
  recurrence5LeadingSquare_coeff_239
  recurrence5LeadingSquare_coeff_240
  recurrence5LeadingSquare_coeff_241
  recurrence5LeadingSquare_coeff_242
  recurrence5LeadingSquare_coeff_243
  recurrence5LeadingSquare_coeff_244
  recurrence5LeadingSquare_coeff_245
  recurrence5LeadingSquare_coeff_246
  recurrence5LeadingSquare_coeff_247
  recurrence5LeadingSquare_coeff_248
  recurrence5LeadingSquare_coeff_249
  recurrence5LeadingSquare_coeff_250
  recurrence5LeadingSquare_coeff_251
  recurrence5LeadingSquare_coeff_252
  recurrence5LeadingSquare_coeff_253
  recurrence5LeadingSquare_coeff_254
  recurrence5LeadingSquare_coeff_255

attribute [local simp]
  recurrence5LeadingSquare_coeff_256
  recurrence5LeadingSquare_coeff_257
  recurrence5LeadingSquare_coeff_258
  recurrence5LeadingSquare_coeff_259
  recurrence5LeadingSquare_coeff_260
  recurrence5LeadingSquare_coeff_261
  recurrence5LeadingSquare_coeff_262
  recurrence5LeadingSquare_coeff_263
  recurrence5LeadingSquare_coeff_264
  recurrence5LeadingSquare_coeff_265
  recurrence5LeadingSquare_coeff_266
  recurrence5LeadingSquare_coeff_267
  recurrence5LeadingSquare_coeff_268
  recurrence5LeadingSquare_coeff_269
  recurrence5LeadingSquare_coeff_270
  recurrence5LeadingSquare_coeff_271
  recurrence5LeadingSquare_coeff_272
  recurrence5LeadingSquare_coeff_273
  recurrence5LeadingSquare_coeff_274
  recurrence5LeadingSquare_coeff_275
  recurrence5LeadingSquare_coeff_276
  recurrence5LeadingSquare_coeff_277
  recurrence5LeadingSquare_coeff_278
  recurrence5LeadingSquare_coeff_279
  recurrence5LeadingSquare_coeff_280
  recurrence5LeadingSquare_coeff_281
  recurrence5LeadingSquare_coeff_282
  recurrence5LeadingSquare_coeff_283
  recurrence5LeadingSquare_coeff_284
  recurrence5LeadingSquare_coeff_285
  recurrence5LeadingSquare_coeff_286
  recurrence5LeadingSquare_coeff_287
  recurrence5LeadingSquare_coeff_288
  recurrence5LeadingSquare_coeff_289
  recurrence5LeadingSquare_coeff_290
  recurrence5A1_coeff_0
  recurrence5A1_coeff_1
  recurrence5A1_coeff_2
  recurrence5A1_coeff_3
  recurrence5A1_coeff_4
  recurrence5A1_coeff_5
  recurrence5A1_coeff_6
  recurrence5A1_coeff_7
  recurrence5A1_coeff_8
  recurrence5A1_coeff_9
  recurrence5A1_coeff_10
  recurrence5A1_coeff_11
  recurrence5A1_coeff_12
  recurrence5A1_coeff_13
  recurrence5A1_coeff_14
  recurrence5A1_coeff_15
  recurrence5A1_coeff_16
  recurrence5A1_coeff_17
  recurrence5A1_coeff_18
  recurrence5A1_coeff_19
  recurrence5A1_coeff_20
  recurrence5A1_coeff_21
  recurrence5A1_coeff_22
  recurrence5A1_coeff_23
  recurrence5A1_coeff_24
  recurrence5A1_coeff_25
  recurrence5A1_coeff_26
  recurrence5A1_coeff_27
  recurrence5A1_coeff_28

attribute [local simp]
  recurrence5A1_coeff_29
  recurrence5A1_coeff_30
  recurrence5A1_coeff_31
  recurrence5A1_coeff_32
  recurrence5A1_coeff_33
  recurrence5A1_coeff_34
  recurrence5A1_coeff_35
  recurrence5A1_coeff_36
  recurrence5A1_coeff_37
  recurrence5A1_coeff_38
  recurrence5A1_coeff_39
  recurrence5A1_coeff_40
  recurrence5A1_coeff_41
  recurrence5A1_coeff_42
  recurrence5A1_coeff_43
  recurrence5A1_coeff_44
  recurrence5A1_coeff_45
  recurrence5A1_coeff_46
  recurrence5A1_coeff_47
  recurrence5A1_coeff_48
  recurrence5A1_coeff_49
  recurrence5A1_coeff_50
  recurrence5A1_coeff_51
  recurrence5A1_coeff_52
  recurrence5A1_coeff_53
  recurrence5A1_coeff_54
  recurrence5A1_coeff_55
  recurrence5A1_coeff_56
  recurrence5A1_coeff_57
  recurrence5A1_coeff_58
  recurrence5A1_coeff_59
  recurrence5A1_coeff_60
  recurrence5A1_coeff_61
  recurrence5A1_coeff_62
  recurrence5A1_coeff_63
  recurrence5A1_coeff_64
  recurrence5A1_coeff_65
  recurrence5A1_coeff_66
  recurrence5A1_coeff_67
  recurrence5A1_coeff_68
  recurrence5A1_coeff_69
  recurrence5A1_coeff_70
  recurrence5A1_coeff_71
  recurrence5A1_coeff_72
  recurrence5A1_coeff_73
  recurrence5A1_coeff_74
  recurrence5A1_coeff_75
  recurrence5A1_coeff_76
  recurrence5A1_coeff_77
  recurrence5A1_coeff_78
  recurrence5A1_coeff_79
  recurrence5A1_coeff_80
  recurrence5A1_coeff_81
  recurrence5A1_coeff_82
  recurrence5A1_coeff_83
  recurrence5A1_coeff_84
  recurrence5A1_coeff_85
  recurrence5A1_coeff_86
  recurrence5A1_coeff_87
  recurrence5A1_coeff_88
  recurrence5A1_coeff_89
  recurrence5A1_coeff_90
  recurrence5A1_coeff_91
  recurrence5A1_coeff_92

attribute [local simp]
  recurrence5A1_coeff_93
  recurrence5A1_coeff_94
  recurrence5A1_coeff_95
  recurrence5A1_coeff_96
  recurrence5A1_coeff_97
  recurrence5A1_coeff_98
  recurrence5A1_coeff_99
  recurrence5A1_coeff_100
  recurrence5A1_coeff_101
  recurrence5A1_coeff_102
  recurrence5A1_coeff_103
  recurrence5A1_coeff_104
  recurrence5A1_coeff_105
  recurrence5A1_coeff_106
  recurrence5A1_coeff_107
  recurrence5A1_coeff_108
  recurrence5A1_coeff_109
  recurrence5A1_coeff_110
  recurrence5A1_coeff_111
  recurrence5A1_coeff_112
  recurrence5A1_coeff_113
  recurrence5A1_coeff_114
  recurrence5A1_coeff_115
  recurrence5A1_coeff_116
  recurrence5A1_coeff_117
  recurrence5A1_coeff_118
  recurrence5A1_coeff_119
  recurrence5A1_coeff_120
  recurrence5A1_coeff_121
  recurrence5A1_coeff_122
  recurrence5A1_coeff_123
  recurrence5A1_coeff_124
  recurrence5A1_coeff_125
  recurrence5A1_coeff_126
  recurrence5A1_coeff_127
  recurrence5A1_coeff_128
  recurrence5A1_coeff_129
  recurrence5A1_coeff_130
  recurrence5A1_coeff_131
  recurrence5A1_coeff_132
  recurrence5A1_coeff_133
  recurrence5A1_coeff_134
  recurrence5A1_coeff_135
  recurrence5A1_coeff_136
  recurrence5A1_coeff_137
  recurrence5A1_coeff_138
  recurrence5A1_coeff_139
  recurrence5A1_coeff_140
  recurrence5A1_coeff_141
  recurrence5A1_coeff_142
  recurrence5A1_coeff_143
  recurrence5A1_coeff_144
  recurrence5A1_coeff_145
  recurrence5A1_coeff_146
  recurrence5A1_coeff_147
  recurrence5A1_coeff_148
  recurrence5A1_coeff_149
  recurrence5A1_coeff_150
  recurrence5A1_coeff_151
  recurrence5A1_coeff_152
  recurrence5A1_coeff_153
  recurrence5A1_coeff_154
  recurrence5A1_coeff_155
  recurrence5A1_coeff_156

attribute [local simp]
  recurrence5A1_coeff_157
  recurrence5A1_coeff_158
  recurrence5A1_coeff_159
  recurrence5A1_coeff_160
  recurrence5A1_coeff_161
  recurrence5A1_coeff_162
  recurrence5A1_coeff_163
  recurrence5A1_coeff_164
  recurrence5A1_coeff_165
  recurrence5A1_coeff_166
  recurrence5A1_coeff_167
  recurrence5A1_coeff_168
  recurrence5A1_coeff_169
  recurrence5A1_coeff_170
  recurrence5A1_coeff_171
  recurrence5A1_coeff_172

theorem recurrence5Scalar1Left_coeff_160 :
    recurrence5Scalar1Left.coeff 160 =
      -((((((36 * 10 ^ 70 +
        4495520119896607890026777768158390479301155724007380986817080513466359) * 10 ^ 70 +
        0246661520038510149196322244523745157346154842427003626010631995266851) * 10 ^ 70 +
        4785330880783474352582147482411970894428388984892167752685481636684512) * 10 ^ 70 +
        3303323910189531912865364680482124920523704078787500279139942795983266) * 10 ^ 70 +
        3517358910810033351302687398979487701091707154451218543460579432472288) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_161 :
    recurrence5Scalar1Left.coeff 161 =
      ((((((84 * 10 ^ 70 +
        1094349239863064045905814353353203142661209529782265831701320307570826) * 10 ^ 70 +
        2817768395662539702783563487517771699331530422786149660610396434070313) * 10 ^ 70 +
        1731783098441118580040662931926325444198330138209874180348481561305648) * 10 ^ 70 +
        7702832564224962327690882801199270802488051885768960106929826111687670) * 10 ^ 70 +
        0184777285900026372698285229978139444444219428332134112577540342609300) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_162 :
    recurrence5Scalar1Left.coeff 162 =
      -((((((190 * 10 ^ 70 +
        5715303978075747311835622168941094108060484689547595367582412980711560) * 10 ^ 70 +
        8895730169429562341661224558117167173010709580372676107297917782824146) * 10 ^ 70 +
        9326788090022128789518861556400473887257702947362121889708919658861204) * 10 ^ 70 +
        6119319979604804207654338326072348333274526017330039307104407032170126) * 10 ^ 70 +
        2600369119531410348198703374608613466801430837229218435690825177365605) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_163 :
    recurrence5Scalar1Left.coeff 163 =
      ((((((423 * 10 ^ 70 +
        9949096915369551762962684927619280600475084708247335245951901255100843) * 10 ^ 70 +
        9641582184841555037254438272409209216063078079547142469180171995120233) * 10 ^ 70 +
        6320051363556099318095985573822892380290595758416846691305384616188921) * 10 ^ 70 +
        8244667800292138607468484768629608634971047377815187486180881421533100) * 10 ^ 70 +
        0236900205453833623709934250808927167967386852349400819872812109819417) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_164 :
    recurrence5Scalar1Left.coeff 164 =
      -((((((926 * 10 ^ 70 +
        3608766401717460907993990459470234958359924866211073886682001450290942) * 10 ^ 70 +
        2880895281626939849305803383215467791756754155544654986124062310562021) * 10 ^ 70 +
        5478004326155703369199140099238583813043243918724978219678606729035357) * 10 ^ 70 +
        8050804267178587255898883708827750335218298193405396689449571077039480) * 10 ^ 70 +
        1028148717038277755043992438931273493064386096630025283384469562969511) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_165 :
    recurrence5Scalar1Left.coeff 165 =
      ((((((1987 * 10 ^ 70 +
        6661557334469863544980073439082915102392096461209805123076066680123834) * 10 ^ 70 +
        1629910467532855610932836718530480317022383818523233298455900422687154) * 10 ^ 70 +
        1962311437621753050366703475831616885788044663435201219127263523202829) * 10 ^ 70 +
        3468122011242625524992998712148653870745801744052023043517285312277375) * 10 ^ 70 +
        9005795789299505598101413668802100188166140373970318968342646660886376) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_166 :
    recurrence5Scalar1Left.coeff 166 =
      -((((((4188 * 10 ^ 70 +
        6705799568581678275384173865474851760249127494507898521336235245971989) * 10 ^ 70 +
        4455390405824250318772494136469818868687479085165520722605247926962586) * 10 ^ 70 +
        9094717517515578777846799256543455556477915208149742875751964922947413) * 10 ^ 70 +
        5922619783547374504004765017650474213680572072527915986932432660361141) * 10 ^ 70 +
        0556334781415320273205376513042821379612546177630420885316623834238205) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_167 :
    recurrence5Scalar1Left.coeff 167 =
      ((((((8669 * 10 ^ 70 +
        6879773860822389276825625431042117833653038182640914690359533095977363) * 10 ^ 70 +
        2977854886360423227383383161214784488248905230979821129698681921451699) * 10 ^ 70 +
        4458553481059905282192126009663656679593292668511577281092627353077958) * 10 ^ 70 +
        4720326273281556443311897487864810423560026326030861668469106928804732) * 10 ^ 70 +
        0229797499053473804012030927393427067159480167923434219140380821905170) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_168 :
    recurrence5Scalar1Left.coeff 168 =
      -((((((17625 * 10 ^ 70 +
        8198018667857599049314812032687246918642295655223267608920830415921240) * 10 ^ 70 +
        1438770314810411572848707979066303854897044268630144026865603919098762) * 10 ^ 70 +
        5200049506553273342630696716565267574072967719283182449901332030148603) * 10 ^ 70 +
        9945935411270919106383186756507763384221516470012082490460472959987214) * 10 ^ 70 +
        1551173355016286673934220341297407162281175618752895065535024595451788) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_169 :
    recurrence5Scalar1Left.coeff 169 =
      ((((((35199 * 10 ^ 70 +
        5419321100695076236844795584346091476891705176635104896012699587911407) * 10 ^ 70 +
        7042612289168975407703521388292599599932757905434005113759519302931523) * 10 ^ 70 +
        3085339278916872124920366669236315284840187885106932751664722595250545) * 10 ^ 70 +
        0983520773542499729265181553079655745027114619149573217713860406088331) * 10 ^ 70 +
        0496589385839929343065998367608926086097710787053842311089977050859614) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_170 :
    recurrence5Scalar1Left.coeff 170 =
      -((((((69054 * 10 ^ 70 +
        0077028988894621589208258538213067220947224469244537610171492961493468) * 10 ^ 70 +
        0912638698118734631626917446815753113732641839380132729999289559841770) * 10 ^ 70 +
        0205294330930850362745095796158459916542774270574111796613655728503710) * 10 ^ 70 +
        7993009531535119354859865461927056067747144716831910615404526849039180) * 10 ^ 70 +
        2275208249292071170580778519681752877471468094892057145796350828994755) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_171 :
    recurrence5Scalar1Left.coeff 171 =
      ((((((133084 * 10 ^ 70 +
        1861342703628448072533377007591867735306201657164629096134501774422300) * 10 ^ 70 +
        2997360128543972129416224324842514379394204229267970568855303053341619) * 10 ^ 70 +
        8136446403228446453436538178431593954604962747046642052722378157915921) * 10 ^ 70 +
        3254062744801557559505321206812778205128942483140929271225505020583830) * 10 ^ 70 +
        1936315250677076382076022635535539663983192667059988272081818496699661) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_172 :
    recurrence5Scalar1Left.coeff 172 =
      -((((((251982 * 10 ^ 70 +
        4716461381519285340630467295866338738964066574257199722854333024096554) * 10 ^ 70 +
        1487568834836043529972450834205149864273990257901861378105256905239990) * 10 ^ 70 +
        8861631544438874945346064981873279258524785435980310616099537608400112) * 10 ^ 70 +
        7266801032954965080695275857468526449947522578704632700456101373116216) * 10 ^ 70 +
        5025756816709015113508998096393145927861691376447062563524594645088193) : ℚ) := by
  unfold recurrence5Scalar1Left
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_173 :
    recurrence5Scalar1Left.coeff 173 =
      ((((((468748 * 10 ^ 70 +
        9187024250402410032400852327176659807089460315345905533431192949820904) * 10 ^ 70 +
        6004249769411865529631080963776731011557247795178697428445380605242801) * 10 ^ 70 +
        5947799789034784528281625694994826900657692450449023944039597709329333) * 10 ^ 70 +
        3823097697015832131647243168829219443209033689881198259844497412215110) * 10 ^ 70 +
        3566739381786632477784167578504220373435502387477046902760738360148008) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 1 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_173_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_174 :
    recurrence5Scalar1Left.coeff 174 =
      -((((((856752 * 10 ^ 70 +
        0877331520314261581005894585696411973992550152564702783907841832725280) * 10 ^ 70 +
        2775338028856579573886554751813236091713834666322547896659072925813210) * 10 ^ 70 +
        7775767247201474929894527125265593550409712106272362093417227334127072) * 10 ^ 70 +
        6481266754584056988017156065191276818635346135446364784786245493059385) * 10 ^ 70 +
        3066976302316962514849173184039587085259229731226411902544288649065715) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 2 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_174_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_175 :
    recurrence5Scalar1Left.coeff 175 =
      ((((((1538625 * 10 ^ 70 +
        7579378827572267150672275933725660163977624919723291402730972624937688) * 10 ^ 70 +
        1078063328111625867667050881495097245909707413907491959535100527976329) * 10 ^ 70 +
        6985849276352307765346539493513905133249327832514672376386939517675244) * 10 ^ 70 +
        7267297045385744744367660273646549119552707620121610432789934645991960) * 10 ^ 70 +
        6635320097135026302769212359911956068650321199162803953855719753177126) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 3 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_175_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_176 :
    recurrence5Scalar1Left.coeff 176 =
      -((((((2715131 * 10 ^ 70 +
        4065208768284932264602367987076397689434571698325498048886922652036396) * 10 ^ 70 +
        0414686986990049854584631928446779595285603466342276145278706396837402) * 10 ^ 70 +
        2345593161870674348259897429935722982407069982557123677943594424875790) * 10 ^ 70 +
        9987202417514451923386630569185227247449166168427830051897000204430582) * 10 ^ 70 +
        2717781709887689699779940742559310153422216020187417820315630478818912) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 4 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_176_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_177 :
    recurrence5Scalar1Left.coeff 177 =
      ((((((4708091 * 10 ^ 70 +
        7558296627167218234345797120351210212223314749478774856161700688607916) * 10 ^ 70 +
        6777263454673447468252887191162541808864513495697607974145112649690880) * 10 ^ 70 +
        6667541870753712548248594814902212954696743867145368154412345262304527) * 10 ^ 70 +
        1376822919409845558971652767798511084125498831898336949948240746424127) * 10 ^ 70 +
        0420096140296308026749958228969198574725709122805287711667976716911225) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 5 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_177_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_178 :
    recurrence5Scalar1Left.coeff 178 =
      -((((((8022513 * 10 ^ 70 +
        3747873284231852252661729683540307471979103611783386537764340807025739) * 10 ^ 70 +
        4114531783357529284664579731298861505861856278524717493464394126279714) * 10 ^ 70 +
        7192742240012449611081916440794710864046971660024021434931548157069651) * 10 ^ 70 +
        6277591487071478179591800094440588654091621321521806718230228517129587) * 10 ^ 70 +
        3739787503568312351758785024105462421351448732717751481928169218160917) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 6 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_178_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_179 :
    recurrence5Scalar1Left.coeff 179 =
      ((((((13433889 * 10 ^ 70 +
        1277987386500101060029195309483666102829399624013896563757325887286449) * 10 ^ 70 +
        5603629302283927878275801365994339799581496218594195194326861597739897) * 10 ^ 70 +
        7338292888295378092148910023806859554699565053716451888478138961673141) * 10 ^ 70 +
        0626962047889974332996914583506904789637936092196054609560397687043301) * 10 ^ 70 +
        2181576662324010334624987819745287268913104745778214520946892613871756) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 7 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_179_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_180 :
    recurrence5Scalar1Left.coeff 180 =
      -((((((22107121 * 10 ^ 70 +
        1724876949610771781400963979308208241838445873426420014570843035566772) * 10 ^ 70 +
        1118665829160190158994225195445277079349132226828382247183689467876281) * 10 ^ 70 +
        7632142721526901866386561747049838246694526161628802181738034075257765) * 10 ^ 70 +
        2845473417836643420208164589652383444875199548704629441216806342116880) * 10 ^ 70 +
        8483771065689580016798887949474737878703680430626532448622844561485573) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 8 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_180_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_181 :
    recurrence5Scalar1Left.coeff 181 =
      ((((((35753132 * 10 ^ 70 +
        2856390691014048885120180342737277519433941868543136379748138476271000) * 10 ^ 70 +
        7549950354668809850032552403873321779368407359204646504622988040306575) * 10 ^ 70 +
        1225773018555075821747163129521750670898773131874433831032731237476601) * 10 ^ 70 +
        6160553654722848536736170513227386697450453889225426790801197402978862) * 10 ^ 70 +
        3842453181775400853844736493559635764448838187828952602188197232294459) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 9 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_181_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_182 :
    recurrence5Scalar1Left.coeff 182 =
      -((((((56827532 * 10 ^ 70 +
        2910358489019605128869472758975426159926683377034065608004240273607172) * 10 ^ 70 +
        6396653176063174275826283654488189221032660865173387738345267733514048) * 10 ^ 70 +
        2334938728639844363158975714434351394360527317093439081027917048815621) * 10 ^ 70 +
        7848674660137194590026657094704784179345798206759136967329445701887638) * 10 ^ 70 +
        2990027287886202703634435124319815241600139943824079070311194504051017) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 10 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_182_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_183 :
    recurrence5Scalar1Left.coeff 183 =
      ((((((88772114 * 10 ^ 70 +
        0254113531405526898483888107020778643367649958725616035938443372461790) * 10 ^ 70 +
        0658913422912560018518491956154136154980187478917781562823218744314992) * 10 ^ 70 +
        3189620637700155048723150951358051652666317038893857428335655133912118) * 10 ^ 70 +
        4904294137854972759598317488029003523874115583043546510825863794297032) * 10 ^ 70 +
        8275987639255310390696413121620440075917593667285316492092832271137228) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 11 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_183_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_184 :
    recurrence5Scalar1Left.coeff 184 =
      -((((((136293943 * 10 ^ 70 +
        0154770624916162156829209192738627710494090122437361648663684267786671) * 10 ^ 70 +
        1861768358039327488039442480384196297219678901079227821826456103294758) * 10 ^ 70 +
        8730421140372025052565957666096543335618248590884961932743260976666805) * 10 ^ 70 +
        8404299386605249568455562160878264503874313602149114838407451063623881) * 10 ^ 70 +
        4285690437914406108422267309924407831355329515935033852898598733788068) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 12 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_184_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_185 :
    recurrence5Scalar1Left.coeff 185 =
      ((((((205668034 * 10 ^ 70 +
        2006255512276024846169486667511888315455924121085770214638546768061485) * 10 ^ 70 +
        7305553031229588337087888629909415323523392153685027645934607082647814) * 10 ^ 70 +
        0538402264401918228351319217209113388475249987724744651509351089411223) * 10 ^ 70 +
        1083837577650655554649990413920884324310392599635240941925595707784096) * 10 ^ 70 +
        7464798208516172172080682791806280459164140150903790620859884273985722) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 13 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_185_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_186 :
    recurrence5Scalar1Left.coeff 186 =
      -((((((305038112 * 10 ^ 70 +
        0767328003233379098785603505419041762853418415868625223869066708873022) * 10 ^ 70 +
        3897183793715417823300166809613095693531094678784443650417730614189594) * 10 ^ 70 +
        9004594481211353678606820767421200972305890481394012867661033514073718) * 10 ^ 70 +
        8045256624735199607751412030472688027979424112167905408002786860435165) * 10 ^ 70 +
        3240224969297943788872349082752707304286994914332529546000915580744803) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 14 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_186_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_187 :
    recurrence5Scalar1Left.coeff 187 =
      ((((((444676353 * 10 ^ 70 +
        7124725726723107383688443403084084553126112801088603236050142324743725) * 10 ^ 70 +
        7081249215358736309638063451300334779259470306464595458167564508779741) * 10 ^ 70 +
        2296399787565970058093234214011580986885082183484641591734050841285327) * 10 ^ 70 +
        9163832424539419550446203677070201884255900294602667403027382227883310) * 10 ^ 70 +
        8481079568943620088740324753785989527231341757790456614813254193294412) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 15 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_187_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_188 :
    recurrence5Scalar1Left.coeff 188 =
      -((((((637148725 * 10 ^ 70 +
        8493460108042361083518973679573979624754909515903900091496468017650715) * 10 ^ 70 +
        4244074335109220500193241438709860834910719804490880331925037741367019) * 10 ^ 70 +
        4280660172490257839151900086220235523305310343541026735207235681920512) * 10 ^ 70 +
        1616551119841907259713449593677045031871670925955755212069221379970346) * 10 ^ 70 +
        8655022302182776059089193144936154615310106570123018823617677037224352) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 16 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_188_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_189 :
    recurrence5Scalar1Left.coeff 189 =
      ((((((897319841 * 10 ^ 70 +
        5915239012598532804836832464411758157356894580495910968382401817943471) * 10 ^ 70 +
        0356577370475946877391040081661244676594882775139394276010271350308333) * 10 ^ 70 +
        8889139989480951911175408856521518089466576080009795750644508487744221) * 10 ^ 70 +
        3675411408614051430367182165872371109108002392015346865881802238932028) * 10 ^ 70 +
        4497791541990165095200551887040521167359902556532539630454044851178854) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 17 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_189_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_190 :
    recurrence5Scalar1Left.coeff 190 =
      -((((((1242123298 * 10 ^ 70 +
        3927900552148069629291995828764241276768860887145737048936154578624524) * 10 ^ 70 +
        6351419433617223497594516530170706315372526146999192558805345352372482) * 10 ^ 70 +
        6267650149838643607732407115949147786577233868004609738127694068250821) * 10 ^ 70 +
        5805849653354306234228792976529527857051704917220867453263574793597074) * 10 ^ 70 +
        2086965967997511418816024828361378018525587761912643108381208068203961) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 18 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_190_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_191 :
    recurrence5Scalar1Left.coeff 191 =
      ((((((1690023872 * 10 ^ 70 +
        7212899545004262440742978333731366532128538649042627817966325191549636) * 10 ^ 70 +
        8264519048632565425202268003978736631952862911651874930320039904162182) * 10 ^ 70 +
        6027680684027130617233298223598933945772109403231537966190462686747416) * 10 ^ 70 +
        8424303957887263387677909745417927004358584110791225190164537060801785) * 10 ^ 70 +
        0622206141796152841236617263900525014521159721510176046043728742243748) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 19 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_191_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_192 :
    recurrence5Scalar1Left.coeff 192 =
      -((((((2260110374 * 10 ^ 70 +
        2378252854120503278660107603300860880930202059394640860449515309472801) * 10 ^ 70 +
        7361878293950574629576110317165702727320471401236872832854509600228341) * 10 ^ 70 +
        1367308112710959325924164125330419265304431388818481604053029054309536) * 10 ^ 70 +
        1896875546543103607310013362327302575132812973629681032681396467257109) * 10 ^ 70 +
        6230601635921635036853969940622497516685773417337658977360771447806708) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 20 +
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_192_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
