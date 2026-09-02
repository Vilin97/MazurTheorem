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

theorem recurrence5Scalar1Left_coeff_67 :
    recurrence5Scalar1Left.coeff 67 =
      -((((65322311607999522257015102071874887802535320955150052650327850868 * 10 ^ 70 +
        7929931348309858620952482726576561009321133603039685962755523377892953) * 10 ^ 70 +
        9253652327543790759233753392398475907012245667306604110682444814779128) * 10 ^ 70 +
        1411982482412362844547698409561670937043881963826160645431471139356983) : ℚ) := by
  unfold recurrence5Scalar1Left
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1Left_coeff_68 :
    recurrence5Scalar1Left.coeff 68 =
      ((((1453871931675380830667610598637699113569411749761514773647468085241 * 10 ^ 70 +
        5004021470911368141535027780184315035685867439755413655440997248380836) * 10 ^ 70 +
        0722271252267402309531552272705501481945285110555294765758701775918185) * 10 ^ 70 +
        6802146597643124006428186660322854113576770095703950681289619957246325) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_69 :
    recurrence5Scalar1Left.coeff 69 =
      -((((30399971393152959913809206974107283082093948098939095627684542202164 * 10 ^ 70 +
        8482874319723034804453653553460446472629219254443631178804631560612906) * 10 ^ 70 +
        7440510176603449341495517843919875426970858109438186156354174232942257) * 10 ^ 70 +
        8957146593134171280961391744179823021027426380800383094912837381316816) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_70 :
    recurrence5Scalar1Left.coeff 70 =
      ((((592929641172971209693047082685843981553255486760194060951411557077354 * 10 ^ 70 +
        0281574671932247658806624169336779512317973996744084595557184051118917) * 10 ^ 70 +
        6761145547547418618491245944295565950142131726282929981181516588051519) * 10 ^ 70 +
        0021286628117129168169428335353362093329476792733685202278774282797802) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_71 :
    recurrence5Scalar1Left.coeff 71 =
      -(((((1 * 10 ^ 70 +
        0653452611440114480188164037109944574465159136706146152337405938592283) * 10 ^ 70 +
        6766319244308503095547107253649931959808541182987506809449869525662642) * 10 ^ 70 +
        4437020297507868367760961523306366174615136142504209461774790396424029) * 10 ^ 70 +
        2779523654114637605280295672685760450426664139249260998279613186487030) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_72 :
    recurrence5Scalar1Left.coeff 72 =
      (((((17 * 10 ^ 70 +
        2115806372968032736656025948022124977050588952329037329645723437243701) * 10 ^ 70 +
        8537039680307297902653397185563775427616061708313245756130810959681143) * 10 ^ 70 +
        2358464634682605184342032652223806968214824396459775031203788639301888) * 10 ^ 70 +
        7427819236582479069926251110102863374779468401572479928188585224044729) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_73 :
    recurrence5Scalar1Left.coeff 73 =
      -(((((236 * 10 ^ 70 +
        4170363997478260546513690537825560458129585043995124258158218336729670) * 10 ^ 70 +
        0713903532947013635385807813022640667257470969727429476907476729676520) * 10 ^ 70 +
        1870739515755853294090080397912014999794189468805722019563812481823722) * 10 ^ 70 +
        0193889205902073314254167558676337502313014880342570572961459018206481) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_74 :
    recurrence5Scalar1Left.coeff 74 =
      (((((2291 * 10 ^ 70 +
        3910732714957148961780694379663311844231446937500324179080591122417429) * 10 ^ 70 +
        7739735394131764231049854334272302849887487119466041215177863184279789) * 10 ^ 70 +
        7672887990784411393017012518016826322945999616006935112798391013970582) * 10 ^ 70 +
        6012951213903249089491930036260701693410108059963619894031226853647019) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_75 :
    recurrence5Scalar1Left.coeff 75 =
      (((((3017 * 10 ^ 70 +
        6425349896099127546826217084447429221776386901190258334783426055877696) * 10 ^ 70 +
        6084657672853625491094109932084136558500566448437467055655371212250179) * 10 ^ 70 +
        6351889721696387888693411340160525353955511234650264424781738860102998) * 10 ^ 70 +
        7906270607747798021012955480056487710969339649026883113298518377120193) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_76 :
    recurrence5Scalar1Left.coeff 76 =
      -(((((934554 * 10 ^ 70 +
        6289065950546705673674851873741692549970464190563416096183542114399118) * 10 ^ 70 +
        8453722033636098335111577879597313727173706053133541324486769990844673) * 10 ^ 70 +
        7216390832452600673497143548010487310816227355218957404656079870950288) * 10 ^ 70 +
        2122772778990639312768529844900833062844523545935636063023145551791413) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_77 :
    recurrence5Scalar1Left.coeff 77 =
      (((((32492598 * 10 ^ 70 +
        6149594036084159890416025556135957522991899992752306429625545183626702) * 10 ^ 70 +
        4425031238940903449227313485752653545039988184312452516435327999431366) * 10 ^ 70 +
        4845627629067650478584765847629245646182771972742616862738312423480792) * 10 ^ 70 +
        7188335164720960917454639669485272363379044791270208270195180097432031) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_78 :
    recurrence5Scalar1Left.coeff 78 =
      -(((((833669724 * 10 ^ 70 +
        9190768471022355750584871975687004527468187221635792337813541661517845) * 10 ^ 70 +
        6889499037267009480382677692257172044217692296014578328311731339256442) * 10 ^ 70 +
        6580211288229424805414296113821432565989550571836802106867038112814640) * 10 ^ 70 +
        0054738721759555633049319399782380413403434147839251672439540082271877) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_79 :
    recurrence5Scalar1Left.coeff 79 =
      (((((18438819119 * 10 ^ 70 +
        9376648313261837576916761839313564373281559830157820472238237152314611) * 10 ^ 70 +
        2965132892021772725684419053630076827523414860261619537787856319045220) * 10 ^ 70 +
        8963673774929728337905437255993365353489823708857845755488812736968339) * 10 ^ 70 +
        0802181855578126171156684417460364359796344119957619901817297391480015) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_80 :
    recurrence5Scalar1Left.coeff 80 =
      -(((((369828556052 * 10 ^ 70 +
        6359386389632025457525440947311973351881596339246664963394906115169090) * 10 ^ 70 +
        3076327151076051264668252899969674562660784848959503670969465210038464) * 10 ^ 70 +
        1399237672105090675324777637057882609637919427695630209043882604150771) * 10 ^ 70 +
        5950012391093390863214824558767472585055898091466609668920073121753220) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_81 :
    recurrence5Scalar1Left.coeff 81 =
      (((((6884128240039 * 10 ^ 70 +
        0797149881088998278908128857509745330709468415579417699710760637509528) * 10 ^ 70 +
        4191125827495342966135822305138744221743837119307936333716008986236226) * 10 ^ 70 +
        8114892914173321207868281232655093332245394736561313728954882597930062) * 10 ^ 70 +
        0434936721484503995327863102159634528527371610080651683338850609457701) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_82 :
    recurrence5Scalar1Left.coeff 82 =
      -(((((120441433072123 * 10 ^ 70 +
        9905726223848722004055114145957769171489781400679294539829896138961977) * 10 ^ 70 +
        2893761769911123724796113644335660492994030501225219172627155062132060) * 10 ^ 70 +
        5400549623332699045120229261604103433090123214000578083664221315483254) * 10 ^ 70 +
        4452164994794769591477237978641062826654749638964900739961283539798582) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_83 :
    recurrence5Scalar1Left.coeff 83 =
      (((((1995975769507973 * 10 ^ 70 +
        7307272392673431779993206013658893801238251014107983847707910416668860) * 10 ^ 70 +
        0172433971238641102522154233254619335107423921057068077285453783190421) * 10 ^ 70 +
        5716855599067799477056245884389125666586910258933238061139394550652636) * 10 ^ 70 +
        9243195105564427237402146703152477089415867030436462855051719135386314) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_84 :
    recurrence5Scalar1Left.coeff 84 =
      -(((((31494518313011337 * 10 ^ 70 +
        9319597612223059463701230352310862176462626860929630448973388848146476) * 10 ^ 70 +
        3177214303455992178961069880654087611386587495231583404956841119056364) * 10 ^ 70 +
        7267693778139915723338365780402806137746400700306719476770698774109397) * 10 ^ 70 +
        8048566731368646196418246755588576425503023962893099175480479741429545) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_85 :
    recurrence5Scalar1Left.coeff 85 =
      (((((474907423653303520 * 10 ^ 70 +
        9454057457180338274084959666028718199268661080507511023707375581525444) * 10 ^ 70 +
        5901703012896518390087492672379201697539533947695648015927789587315975) * 10 ^ 70 +
        5407900936414870862405510207230746017116750020561744817127139567344274) * 10 ^ 70 +
        7189067542372058493486095475074858132616540430300534384976367447721628) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_86 :
    recurrence5Scalar1Left.coeff 86 =
      -(((((6862215882538499669 * 10 ^ 70 +
        5292312653636286656140781450873798633618586900680783065969271838957079) * 10 ^ 70 +
        2691165316057702611924049316946366215639146103199172418593450448820316) * 10 ^ 70 +
        2451889264750980955832902309551442033306468439459085838026968170711394) * 10 ^ 70 +
        1503335933918407787752768424891290758552598875120980534275948855387351) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_87 :
    recurrence5Scalar1Left.coeff 87 =
      (((((95218531596786895216 * 10 ^ 70 +
        0786814856319311013022512775386047354464935103004255350707022203528929) * 10 ^ 70 +
        3693905497688111019568767093147381307742650599586018986600108574270011) * 10 ^ 70 +
        0929661378981618238369297808186582406714334495503578659380257241243843) * 10 ^ 70 +
        9185485183107929353057806363787624424613987017930652030593921316791409) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_88 :
    recurrence5Scalar1Left.coeff 88 =
      -(((((1270918414539887881823 * 10 ^ 70 +
        9209623838057775583370012905103918647252490972730736658238230817158729) * 10 ^ 70 +
        7306059741646003945551101970753794671213508156115200040445709105974088) * 10 ^ 70 +
        5247599009717765836796593530742241048641525655630241007638090017429211) * 10 ^ 70 +
        0900129485626805580378739145093150440968248729427912370258921950997738) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_89 :
    recurrence5Scalar1Left.coeff 89 =
      (((((16340318316422497564258 * 10 ^ 70 +
        2845604850975702761602492060375753974628723301853231928821885775831584) * 10 ^ 70 +
        4479598967337581327811180289110904646739602167598451810759259621776176) * 10 ^ 70 +
        6826862399242456166930502457260396507263072638748321047576824472756701) * 10 ^ 70 +
        4507781645475558681497944486244627414317832469287583636894147729728451) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_90 :
    recurrence5Scalar1Left.coeff 90 =
      -(((((202610760203990237436639 * 10 ^ 70 +
        4940593390135027129948271732419295086110703634488770890464857916150864) * 10 ^ 70 +
        4324548389553067669252858669448933803276242682879837550454473757159683) * 10 ^ 70 +
        1251505808775049620875887413254756316162694384009090941601818040209191) * 10 ^ 70 +
        6005066068560409430503037187286061342587723430232529404538660014289960) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_91 :
    recurrence5Scalar1Left.coeff 91 =
      (((((2425295877369027007595872 * 10 ^ 70 +
        7953389707071343059581551889751180668366891213387903437710222641889583) * 10 ^ 70 +
        4505543093295736717989622860131260202060533265368508233971467251189131) * 10 ^ 70 +
        8521244287239191949226847089819455306103199590989667673065412537679499) * 10 ^ 70 +
        4251480759260999889356296545996138457958373307591086308354048758691028) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_92 :
    recurrence5Scalar1Left.coeff 92 =
      -(((((28051321904694607365787608 * 10 ^ 70 +
        9085770915309548163172186837688691849671253517286589042986599525247641) * 10 ^ 70 +
        2157465002989958484658129544549864395917642948816605569269071714788971) * 10 ^ 70 +
        5092572005305185042721167971000674091099147979314430213670600604604219) * 10 ^ 70 +
        5347438144355295021923876098807121353920512400397993183334299670356675) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_93 :
    recurrence5Scalar1Left.coeff 93 =
      (((((313741067096397553658635452 * 10 ^ 70 +
        9350362614430659435868061936827051980201817545343510560328186537635701) * 10 ^ 70 +
        0824180080940945276222876331977081462793374600731817115254171378121354) * 10 ^ 70 +
        5107172530564353712565413698794707418771750152361670840707429801304500) * 10 ^ 70 +
        8312232346191939929438358447664917278390534588142355247007068898348304) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_94 :
    recurrence5Scalar1Left.coeff 94 =
      -(((((3395685434994574243557701819 * 10 ^ 70 +
        8539631468602711172072933484535165176527001341620723744709922596819653) * 10 ^ 70 +
        3198316757160194135806517135636887823410430170367677231011995863688734) * 10 ^ 70 +
        7715852838331982162551410026843253706424957638941362147399258204377210) * 10 ^ 70 +
        7719316856305094305367013955177995189130780366571846434973825638837230) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_95 :
    recurrence5Scalar1Left.coeff 95 =
      (((((35587887646394048837877311195 * 10 ^ 70 +
        1719271585514206642904968389260288291274559693262588496592335065309992) * 10 ^ 70 +
        6662007350814931398174456186379870662148599287625997476009958002764038) * 10 ^ 70 +
        9073939441914954131412138911802629099706360865773387592983535459465959) * 10 ^ 70 +
        0646394505551561227126752327181814944930954692918917316874310984549733) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_96 :
    recurrence5Scalar1Left.coeff 96 =
      -(((((361370922216648746447133854039 * 10 ^ 70 +
        1198381343583770479562378637004416581557632880862181548650180060816407) * 10 ^ 70 +
        6616770295900801986489269997714965629103376291630148280351646779934427) * 10 ^ 70 +
        0641298164857670149615735434236760784426367623395821656442623373295837) * 10 ^ 70 +
        9592607778725169574437625221580216111321933235438600739098955924197594) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_97 :
    recurrence5Scalar1Left.coeff 97 =
      (((((3557285312975617484758018711022 * 10 ^ 70 +
        0951918780511969722679372641655468207279155788201023031147315245814223) * 10 ^ 70 +
        8257035857228422339464521369771504562989528972466996504746674006619601) * 10 ^ 70 +
        6180607257989071050696725449001689161856587404056652056894819766691059) * 10 ^ 70 +
        1398874988782590344085480471852860478723152844319851033554452891011197) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_98 :
    recurrence5Scalar1Left.coeff 98 =
      -(((((33964140792787174666392391918582 * 10 ^ 70 +
        6289418117930730139326853816133462717934093225208744422299125744032862) * 10 ^ 70 +
        4401451449963607156926125961261939033715572218882644823361116709323359) * 10 ^ 70 +
        7710621174845698109517686975175723740345261710589310139410931388325885) * 10 ^ 70 +
        9815763848500939680147121214930633461405302265081695481760390909439888) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_99 :
    recurrence5Scalar1Left.coeff 99 =
      (((((314678412619655541767692219809019 * 10 ^ 70 +
        3908303765696819813200231440526971162478314904027414633834437956662809) * 10 ^ 70 +
        8952349429576932266162692580651824930602148205651708387387791468997074) * 10 ^ 70 +
        8207757145886320891426130739982179296489821379489899283162168218738727) * 10 ^ 70 +
        3062226381139052105817549264537951737816064603091188906386900537854339) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_100 :
    recurrence5Scalar1Left.coeff 100 =
      -(((((2830436974725472991987016514489086 * 10 ^ 70 +
        3907536224350514375844008745410037232137028950697368791198593546849266) * 10 ^ 70 +
        1197039386644742960848394288584852179295623843620540325948786936138456) * 10 ^ 70 +
        6459317461280940792499606250762733069155585297154176237933210775847779) * 10 ^ 70 +
        7790533415769053932627929869270900354235858369671804367009509794353224) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_101 :
    recurrence5Scalar1Left.coeff 101 =
      (((((24726661861241066038542243880427302 * 10 ^ 70 +
        3004057719366055304341797116119911347776217513333546027484615759385292) * 10 ^ 70 +
        2212043717898614075734318992208932365344462875682289375853381239349386) * 10 ^ 70 +
        1591863368777704261247756823915894840359414555177183836829555365569594) * 10 ^ 70 +
        1886411343602167115211872174081799521948168682756050048759609990816725) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_102 :
    recurrence5Scalar1Left.coeff 102 =
      -(((((209883765520524979316936944397163390 * 10 ^ 70 +
        1985470020761472490228579745466937636315439652557675972420663661829807) * 10 ^ 70 +
        3401751981481750651304364984175664896155157186357990973340397269690031) * 10 ^ 70 +
        4364037609922497443728102201914926108861926933216270495046859006886903) * 10 ^ 70 +
        7403656665431250643240550957737060267156603766439585582993638549420949) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_103 :
    recurrence5Scalar1Left.coeff 103 =
      (((((1731654043673431435760826803505657364 * 10 ^ 70 +
        0161403966320634385235235440926123720359868799842426348433742546621248) * 10 ^ 70 +
        1353186823581184904163405620155294526365291857556210352884037524314227) * 10 ^ 70 +
        7373512094625517685692062745461067046475227225306521580146494127281892) * 10 ^ 70 +
        8572883099625808790218959169222663563293721736912314702839825775738001) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_104 :
    recurrence5Scalar1Left.coeff 104 =
      -(((((13892245295145770288241548319869637832 * 10 ^ 70 +
        5994451111488042761268749687324513325589169332738451571098066106842985) * 10 ^ 70 +
        2715236052833256056336068260696683777848922205842829776758601575164207) * 10 ^ 70 +
        1578427922450325800562100089617310871724724842287071009279227159343414) * 10 ^ 70 +
        1597469822651298755190900012260911227121283970448241917153294418906639) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_105 :
    recurrence5Scalar1Left.coeff 105 =
      (((((108409197655182449996513089308565399420 * 10 ^ 70 +
        4234602968902509164147014566420350249540359080367154118479799279391282) * 10 ^ 70 +
        5321379450479424796908310704380624513252336982850706390775813248653049) * 10 ^ 70 +
        2753492208937700902820349709202758502627152077793147161566559622325157) * 10 ^ 70 +
        6600275239741806719745927357913486705442402402685036408642634461260561) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_106 :
    recurrence5Scalar1Left.coeff 106 =
      -(((((823169733020287156597711057668532981573 * 10 ^ 70 +
        4375076972934874203914053184403328253408753429407094427152244459863513) * 10 ^ 70 +
        4236698282195948950871447129578111584877169205421801191948943229568217) * 10 ^ 70 +
        3757596896555492826258418449879606405424962444303615974985701864078433) * 10 ^ 70 +
        1366995341724210838195214961841086509630952276445687984651351308938607) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_107 :
    recurrence5Scalar1Left.coeff 107 =
      (((((6083924310938660436007301902270578654753 * 10 ^ 70 +
        0410570449484902829867253628187355439804382900489262999193147625645200) * 10 ^ 70 +
        6931434597472380389624847492658552485974637621636495967449139367266637) * 10 ^ 70 +
        1284203538684370518610454828446681028303971377522758275241936152101898) * 10 ^ 70 +
        0140476652283793776995602397885768927318059828675031516733282539851833) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_108 :
    recurrence5Scalar1Left.coeff 108 =
      -(((((43781006019557426980776134033951005862087 * 10 ^ 70 +
        1097378325897938540641359968786116379085583008201272828930716218525227) * 10 ^ 70 +
        2352152264070254317892702317718520673940829453110895020167065226094559) * 10 ^ 70 +
        8627797102426127069314775653677031525500662099939914542423656412750334) * 10 ^ 70 +
        3918517703700784459553956183659409358642243596686856337350924078508113) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_109 :
    recurrence5Scalar1Left.coeff 109 =
      (((((306850452798320449209189622652658633949118 * 10 ^ 70 +
        2247993880178202616240714073348708244362972167703961021569252361350413) * 10 ^ 70 +
        2254659733585045737227677620070806345878808750897622930367273798078359) * 10 ^ 70 +
        8724092609875956112235832129184615663511263578171605432844144089954670) * 10 ^ 70 +
        1522195732923551859333502103423318159313157990778855036281443350741171) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_110 :
    recurrence5Scalar1Left.coeff 110 =
      -(((((2095241041946197737511570111658183420108665 * 10 ^ 70 +
        0309021490500283268305854270788746134647577749300339135418858379107890) * 10 ^ 70 +
        1752110058895067937335955193165975369531499760032367019012566793692636) * 10 ^ 70 +
        7765247075680390432405857931295317129461515913282881138647681063889448) * 10 ^ 70 +
        6242253600476423650744012446562298280708200854177677811635985949458298) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_111 :
    recurrence5Scalar1Left.coeff 111 =
      (((((13942168137126326070552544952432861040845036 * 10 ^ 70 +
        3559782672928872145519590819399805241515924240997916021440279717625669) * 10 ^ 70 +
        8244792133204631028353900496250225445490194701065599941264335007967267) * 10 ^ 70 +
        0387335960559085791784005318218733975071526983670079546493787631663856) * 10 ^ 70 +
        2366574047462217393810474200851149880029473615056289565603373445611117) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_112 :
    recurrence5Scalar1Left.coeff 112 =
      -(((((90434618540822392598974856745996858417926091 * 10 ^ 70 +
        1953885187769902138044713721169973189839293165595595323327485109187944) * 10 ^ 70 +
        8964295632890606702607056498956037291631727489230816323929926393900093) * 10 ^ 70 +
        9654385637845048405411558501519743936794785986386392034138931118480194) * 10 ^ 70 +
        0426824530935085626976744930107174920591984901774058903928027442209948) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_113 :
    recurrence5Scalar1Left.coeff 113 =
      (((((571955763095718681289508009162868346054867267 * 10 ^ 70 +
        9694872032141766771729830888478400890233958702904898296830099277991042) * 10 ^ 70 +
        9874899405501282494369968027585489825328647110942618294071808859735120) * 10 ^ 70 +
        4724754434232924554147961336127155390359405157948645280078657242432200) * 10 ^ 70 +
        7785158218777942161484992340534722142204111713640629266135927363915160) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_114 :
    recurrence5Scalar1Left.coeff 114 =
      -(((((3527973013726986462382328183712486402522913442 * 10 ^ 70 +
        2945597752164304635661841696956638985261327073009571562299061746449885) * 10 ^ 70 +
        8075561194032833578889333970424859334117994325730471095706429473133371) * 10 ^ 70 +
        8951041176780198057447051375518007306523244267730545321084417313854048) * 10 ^ 70 +
        9554283846300825164398011684263929120206146057270120763966683565321471) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_115 :
    recurrence5Scalar1Left.coeff 115 =
      (((((21229099359812947557914681527450471696208119331 * 10 ^ 70 +
        5809903244092601523697860657663359208229463790921314153715155637846404) * 10 ^ 70 +
        2664711875670404371847948104267614644464920718876756381409698733369010) * 10 ^ 70 +
        1156408686235553065329893879721966872275672108145712768043874429896237) * 10 ^ 70 +
        0921436981566777203382891381892251646488094519547839767739179988439886) : ℚ) := by
  unfold recurrence5Scalar1Left
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

theorem recurrence5Scalar1Left_coeff_116 :
    recurrence5Scalar1Left.coeff 116 =
      -(((((124648376721657355756642792040412395628265043624 * 10 ^ 70 +
        7461169392715613719356080940514478784771142971453016357545996402420317) * 10 ^ 70 +
        5532041418951741397358671610896983275857237063743292866683416582266371) * 10 ^ 70 +
        3244847823823763191695477132947310256062735852764730471079346031294983) * 10 ^ 70 +
        2364103193877311651966889545037379897128536880870758255823911518537910) : ℚ) := by
  unfold recurrence5Scalar1Left
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

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
