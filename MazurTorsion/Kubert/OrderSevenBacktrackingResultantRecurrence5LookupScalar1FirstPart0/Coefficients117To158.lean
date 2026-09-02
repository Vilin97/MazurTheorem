/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1FirstPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1First coefficient convolution

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
  recurrence5B2A3_coeff_0
  recurrence5B2A3_coeff_1
  recurrence5B2A3_coeff_2
  recurrence5B2A3_coeff_3
  recurrence5B2A3_coeff_4
  recurrence5B2A3_coeff_5
  recurrence5B2A3_coeff_6
  recurrence5B2A3_coeff_7
  recurrence5B2A3_coeff_8
  recurrence5B2A3_coeff_9
  recurrence5B2A3_coeff_10
  recurrence5B2A3_coeff_11
  recurrence5B2A3_coeff_12
  recurrence5B2A3_coeff_13
  recurrence5B2A3_coeff_14
  recurrence5B2A3_coeff_15
  recurrence5B2A3_coeff_16
  recurrence5B2A3_coeff_17
  recurrence5B2A3_coeff_18
  recurrence5B2A3_coeff_19
  recurrence5B2A3_coeff_20
  recurrence5B2A3_coeff_21
  recurrence5B2A3_coeff_22
  recurrence5B2A3_coeff_23
  recurrence5B2A3_coeff_24
  recurrence5B2A3_coeff_25
  recurrence5B2A3_coeff_26
  recurrence5B2A3_coeff_27
  recurrence5B2A3_coeff_28
  recurrence5B2A3_coeff_29
  recurrence5B2A3_coeff_30
  recurrence5B2A3_coeff_31
  recurrence5B2A3_coeff_32
  recurrence5B2A3_coeff_33
  recurrence5B2A3_coeff_34
  recurrence5B2A3_coeff_35
  recurrence5B2A3_coeff_36
  recurrence5B2A3_coeff_37

attribute [local simp]
  recurrence5B2A3_coeff_38
  recurrence5B2A3_coeff_39
  recurrence5B2A3_coeff_40
  recurrence5B2A3_coeff_41
  recurrence5B2A3_coeff_42
  recurrence5B2A3_coeff_43
  recurrence5B2A3_coeff_44
  recurrence5B2A3_coeff_45
  recurrence5B2A3_coeff_46
  recurrence5B2A3_coeff_47
  recurrence5B2A3_coeff_48
  recurrence5B2A3_coeff_49
  recurrence5B2A3_coeff_50
  recurrence5B2A3_coeff_51
  recurrence5B2A3_coeff_52
  recurrence5B2A3_coeff_53
  recurrence5B2A3_coeff_54
  recurrence5B2A3_coeff_55
  recurrence5B2A3_coeff_56
  recurrence5B2A3_coeff_57
  recurrence5B2A3_coeff_58
  recurrence5B2A3_coeff_59
  recurrence5B2A3_coeff_60
  recurrence5B2A3_coeff_61
  recurrence5B2A3_coeff_62
  recurrence5B2A3_coeff_63
  recurrence5B2A3_coeff_64
  recurrence5B2A3_coeff_65
  recurrence5B2A3_coeff_66
  recurrence5B2A3_coeff_67
  recurrence5B2A3_coeff_68
  recurrence5B2A3_coeff_69
  recurrence5B2A3_coeff_70
  recurrence5B2A3_coeff_71
  recurrence5B2A3_coeff_72
  recurrence5B2A3_coeff_73
  recurrence5B2A3_coeff_74
  recurrence5B2A3_coeff_75
  recurrence5B2A3_coeff_76
  recurrence5B2A3_coeff_77
  recurrence5B2A3_coeff_78
  recurrence5B2A3_coeff_79
  recurrence5B2A3_coeff_80
  recurrence5B2A3_coeff_81
  recurrence5B2A3_coeff_82
  recurrence5B2A3_coeff_83
  recurrence5B2A3_coeff_84
  recurrence5B2A3_coeff_85
  recurrence5B2A3_coeff_86
  recurrence5B2A3_coeff_87
  recurrence5B2A3_coeff_88
  recurrence5B2A3_coeff_89
  recurrence5B2A3_coeff_90
  recurrence5B2A3_coeff_91
  recurrence5B2A3_coeff_92
  recurrence5B2A3_coeff_93
  recurrence5B2A3_coeff_94
  recurrence5B2A3_coeff_95
  recurrence5B2A3_coeff_96
  recurrence5B2A3_coeff_97
  recurrence5B2A3_coeff_98
  recurrence5B2A3_coeff_99
  recurrence5B2A3_coeff_100
  recurrence5B2A3_coeff_101

attribute [local simp]
  recurrence5B2A3_coeff_102
  recurrence5B2A3_coeff_103
  recurrence5B2A3_coeff_104
  recurrence5B2A3_coeff_105
  recurrence5B2A3_coeff_106
  recurrence5B2A3_coeff_107
  recurrence5B2A3_coeff_108
  recurrence5B2A3_coeff_109
  recurrence5B2A3_coeff_110
  recurrence5B2A3_coeff_111
  recurrence5B2A3_coeff_112
  recurrence5B2A3_coeff_113
  recurrence5B2A3_coeff_114
  recurrence5B2A3_coeff_115
  recurrence5B2A3_coeff_116
  recurrence5B2A3_coeff_117
  recurrence5B2A3_coeff_118
  recurrence5B2A3_coeff_119
  recurrence5B2A3_coeff_120
  recurrence5B2A3_coeff_121
  recurrence5B2A3_coeff_122
  recurrence5B2A3_coeff_123
  recurrence5B2A3_coeff_124
  recurrence5B2A3_coeff_125
  recurrence5B2A3_coeff_126
  recurrence5B2A3_coeff_127
  recurrence5B2A3_coeff_128
  recurrence5B2A3_coeff_129
  recurrence5B2A3_coeff_130
  recurrence5B2A3_coeff_131
  recurrence5B2A3_coeff_132
  recurrence5B2A3_coeff_133
  recurrence5B2A3_coeff_134
  recurrence5B2A3_coeff_135
  recurrence5B2A3_coeff_136
  recurrence5B2A3_coeff_137
  recurrence5B2A3_coeff_138
  recurrence5B2A3_coeff_139
  recurrence5B2A3_coeff_140
  recurrence5B2A3_coeff_141
  recurrence5B2A3_coeff_142
  recurrence5B2A3_coeff_143
  recurrence5B2A3_coeff_144
  recurrence5B2A3_coeff_145
  recurrence5B2A3_coeff_146
  recurrence5B2A3_coeff_147
  recurrence5B2A3_coeff_148
  recurrence5B2A3_coeff_149
  recurrence5B2A3_coeff_150
  recurrence5B2A3_coeff_151
  recurrence5B2A3_coeff_152
  recurrence5B2A3_coeff_153
  recurrence5B2A3_coeff_154
  recurrence5B2A3_coeff_155
  recurrence5B2A3_coeff_156
  recurrence5B2A3_coeff_157
  recurrence5B2A3_coeff_158
  recurrence5B2A3_coeff_159
  recurrence5B2A3_coeff_160
  recurrence5B2A3_coeff_161
  recurrence5B2A3_coeff_162
  recurrence5B2A3_coeff_163
  recurrence5B2A3_coeff_164
  recurrence5B2A3_coeff_165

attribute [local simp]
  recurrence5B2A3_coeff_166
  recurrence5B2A3_coeff_167
  recurrence5B2A3_coeff_168
  recurrence5B2A3_coeff_169
  recurrence5B2A3_coeff_170
  recurrence5B2A3_coeff_171
  recurrence5B2A3_coeff_172
  recurrence5B2A3_coeff_173
  recurrence5B2A3_coeff_174
  recurrence5B2A3_coeff_175
  recurrence5B2A3_coeff_176
  recurrence5B2A3_coeff_177
  recurrence5B2A3_coeff_178
  recurrence5B2A3_coeff_179
  recurrence5B2A3_coeff_180
  recurrence5B2A3_coeff_181
  recurrence5B2A3_coeff_182
  recurrence5B2A3_coeff_183
  recurrence5B2A3_coeff_184
  recurrence5B2A3_coeff_185
  recurrence5B2A3_coeff_186
  recurrence5B2A3_coeff_187
  recurrence5B2A3_coeff_188
  recurrence5B2A3_coeff_189
  recurrence5B2A3_coeff_190
  recurrence5B2A3_coeff_191
  recurrence5B2A3_coeff_192
  recurrence5B2A3_coeff_193
  recurrence5B2A3_coeff_194
  recurrence5B2A3_coeff_195
  recurrence5B2A3_coeff_196
  recurrence5B2A3_coeff_197
  recurrence5B2A3_coeff_198
  recurrence5B2A3_coeff_199
  recurrence5B2A3_coeff_200
  recurrence5B2A3_coeff_201
  recurrence5B2A3_coeff_202
  recurrence5B2A3_coeff_203
  recurrence5B2A3_coeff_204
  recurrence5B2A3_coeff_205
  recurrence5B2A3_coeff_206
  recurrence5B2A3_coeff_207
  recurrence5B2A3_coeff_208
  recurrence5B2A3_coeff_209
  recurrence5B2A3_coeff_210
  recurrence5B2A3_coeff_211
  recurrence5B2A3_coeff_212
  recurrence5B2A3_coeff_213
  recurrence5B2A3_coeff_214
  recurrence5B2A3_coeff_215
  recurrence5B2A3_coeff_216
  recurrence5B2A3_coeff_217
  recurrence5B2A3_coeff_218
  recurrence5B2A3_coeff_219
  recurrence5B2A3_coeff_220
  recurrence5B2A3_coeff_221
  recurrence5B2A3_coeff_222
  recurrence5B2A3_coeff_223
  recurrence5B2A3_coeff_224
  recurrence5B2A3_coeff_225
  recurrence5B2A3_coeff_226
  recurrence5B2A3_coeff_227
  recurrence5B2A3_coeff_228
  recurrence5B2A3_coeff_229

attribute [local simp]
  recurrence5B2A3_coeff_230
  recurrence5B2A3_coeff_231
  recurrence5B2A3_coeff_232
  recurrence5B2A3_coeff_233
  recurrence5B2A3_coeff_234
  recurrence5B2A3_coeff_235
  recurrence5B2A3_coeff_236
  recurrence5B2A3_coeff_237
  recurrence5B2A3_coeff_238
  recurrence5B2A3_coeff_239
  recurrence5B2A3_coeff_240
  recurrence5B2A3_coeff_241
  recurrence5B2A3_coeff_242
  recurrence5B2A3_coeff_243
  recurrence5B2A3_coeff_244
  recurrence5B2A3_coeff_245
  recurrence5B2A3_coeff_246
  recurrence5B2A3_coeff_247
  recurrence5B2A3_coeff_248
  recurrence5B2A3_coeff_249
  recurrence5B2A3_coeff_250
  recurrence5B2A3_coeff_251
  recurrence5B2A3_coeff_252
  recurrence5B2A3_coeff_253
  recurrence5B2A3_coeff_254
  recurrence5B2A3_coeff_255
  recurrence5B2A3_coeff_256
  recurrence5B2A3_coeff_257
  recurrence5B2A3_coeff_258
  recurrence5B2A3_coeff_259
  recurrence5B2A3_coeff_260
  recurrence5B2A3_coeff_261
  recurrence5B2A3_coeff_262
  recurrence5B2A3_coeff_263
  recurrence5B2A3_coeff_264
  recurrence5B2A3_coeff_265
  recurrence5B2A3_coeff_266
  recurrence5B2A3_coeff_267
  recurrence5B2A3_coeff_268
  recurrence5B2A3_coeff_269
  recurrence5B2A3_coeff_270
  recurrence5B2A3_coeff_271
  recurrence5B2A3_coeff_272
  recurrence5B2A3_coeff_273
  recurrence5B2A3_coeff_274
  recurrence5B2A3_coeff_275
  recurrence5B2A3_coeff_276
  recurrence5B2A3_coeff_277
  recurrence5B2A3_coeff_278
  recurrence5B2A3_coeff_279
  recurrence5B2A3_coeff_280
  recurrence5B2A3_coeff_281
  recurrence5B2A3_coeff_282
  recurrence5B2A3_coeff_283
  recurrence5B2A3_coeff_284
  recurrence5B2A3_coeff_285
  recurrence5B2A3_coeff_286
  recurrence5B2A3_coeff_287
  recurrence5B2A3_coeff_288
  recurrence5B2A3_coeff_289
  recurrence5B2A3_coeff_290
  recurrence5B2A3_coeff_291
  recurrence5B2A3_coeff_292
  recurrence5B2A3_coeff_293

attribute [local simp]
  recurrence5B2A3_coeff_294
  recurrence5B2A3_coeff_295
  recurrence5B2A3_coeff_296
  recurrence5B2A3_coeff_297
  recurrence5B2A3_coeff_298
  recurrence5B2A3_coeff_299
  recurrence5B2A3_coeff_300
  recurrence5B2A3_coeff_301
  recurrence5B2A3_coeff_302
  recurrence5B2A3_coeff_303
  recurrence5B2A3_coeff_304
  recurrence5B2A3_coeff_305
  recurrence5B2A3_coeff_306
  recurrence5B2A3_coeff_307
  recurrence5B2A3_coeff_308
  recurrence5B2A3_coeff_309

theorem recurrence5Scalar1First_coeff_117 :
    recurrence5Scalar1First.coeff 117 =
      (((((237646026576916323142159305505773476485835224571 * 10 ^ 70 +
        8613691266137006802961787565702766496399889845046602245129715956636385) * 10 ^ 70 +
        9223431058271011831796230287694702491809473113888889135181633887118307) * 10 ^ 70 +
        6098612151814847845257159417051244335946046101446811853401263788283560) * 10 ^ 70 +
        5108930756229859381856424183990683105863129095381284164641651217975088) : ℚ) := by
  unfold recurrence5Scalar1First
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

theorem recurrence5Scalar1First_coeff_118 :
    recurrence5Scalar1First.coeff 118 =
      -(((((1330280180370450205150764660376989934139820117975 * 10 ^ 70 +
        0082236062389431965503685812274531019508543164172889478894561477169899) * 10 ^ 70 +
        3872703163741254815105304395731832102826810628585372896390737096849139) * 10 ^ 70 +
        9291790205629669455779030033417565844915691376372973447273466624582268) * 10 ^ 70 +
        6552515872149168545656321479550771555726148660294220119615614793658245) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_119 :
    recurrence5Scalar1First.coeff 119 =
      (((((7272266355494638331037925983937536637222976521770 * 10 ^ 70 +
        0798598154457130698263694376921001515561770012990320353849997399108717) * 10 ^ 70 +
        7330904451208774527801556154035706854835195427406181608727263298669552) * 10 ^ 70 +
        3831394700254136506591377572116634855893146146936002292960179312327626) * 10 ^ 70 +
        7026916716536892503032170663408285116714901250532434533773983984284518) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_120 :
    recurrence5Scalar1First.coeff 120 =
      -(((((38833352768780641988552009877088242496733102179117 * 10 ^ 70 +
        3594607779037697614562105462954184417121915460067778645483163673064375) * 10 ^ 70 +
        4903904115708125613771829567897361225166303762421254434920130480743999) * 10 ^ 70 +
        7319381218514945093692192210475492515979347346980287583681146905441155) * 10 ^ 70 +
        8312770343661261425395944944724506485654940398882977339314475151557020) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_121 :
    recurrence5Scalar1First.coeff 121 =
      (((((202600307778675469327256794123751652252418494501117 * 10 ^ 70 +
        5649569134888802155265165255230218937933578814425733047137191929865742) * 10 ^ 70 +
        2026187660788669682069787065570511476973236655041090534561728925911744) * 10 ^ 70 +
        9275826715701668377423592451924393225682770449479792932328909589572267) * 10 ^ 70 +
        0906389266401998449660522559469793983125311591957350440647025437625660) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_122 :
    recurrence5Scalar1First.coeff 122 =
      -(((((1032914670540623043165963127081155624524320071923266 * 10 ^ 70 +
        3435283690616223900553250748634925401765185893526011699776735393205308) * 10 ^ 70 +
        0959649152457199628686781689878335775424683215706116407375716316147056) * 10 ^ 70 +
        7904445884223871714193498858710721551908466390239923299843214508661309) * 10 ^ 70 +
        9721794821195415530052073087629932184635202256554791853826277629201401) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_123 :
    recurrence5Scalar1First.coeff 123 =
      (((((5147121573453632676401979455320828276077854748277307 * 10 ^ 70 +
        9710458802733872548686133111328131204418942276900135101712729843789308) * 10 ^ 70 +
        1630214470815379354157425514587670317110577416392032010633075153012011) * 10 ^ 70 +
        9857938406559710216476171610049727544756587747285211405966346880101179) * 10 ^ 70 +
        4738313247510499665409547849476976300401813889387622300951530585406946) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_124 :
    recurrence5Scalar1First.coeff 124 =
      -(((((25074027740475403672535174177473867710587967198418653 * 10 ^ 70 +
        7070988426158636875174339159847431437298838308187728949782309445286628) * 10 ^ 70 +
        8861220847722989791837672019799538741576080308218292220558199414297799) * 10 ^ 70 +
        9147187687703956469551615644351215341513511006393214513790533459293837) * 10 ^ 70 +
        3830258892881906997960175181688373447085033840027252786206681001042205) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_125 :
    recurrence5Scalar1First.coeff 125 =
      (((((119433227086100633611920922243482802698455394320532468 * 10 ^ 70 +
        6101567243181590107344407625541643674558424904343648982356369646908614) * 10 ^ 70 +
        1322995614392786935866857719370487123861071557324867616129579667448688) * 10 ^ 70 +
        4070767205315009449701700294239185982460620590218788452125154392290019) * 10 ^ 70 +
        3378642794897760615163645267526268881563779774266990220685090518434848) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_126 :
    recurrence5Scalar1First.coeff 126 =
      -(((((556348630350420261706776755529187260376743096750650301 * 10 ^ 70 +
        2565617552240666366909771961103504694679591945260117255703130015564754) * 10 ^ 70 +
        3607910443789886135740124071428488936690583921180589737878527061155887) * 10 ^ 70 +
        1457134230723106746019657007571862263526435214089882322411740635871789) * 10 ^ 70 +
        5590811631687521830587217941649098973486444006052754636083480702390515) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_127 :
    recurrence5Scalar1First.coeff 127 =
      (((((2534935120339289174005942527583964520810317399941687057 * 10 ^ 70 +
        0058399921522799968719763744069752361999960293078715859732533621396627) * 10 ^ 70 +
        1342192916159879662540031017476547980599446924424056350744486647228733) * 10 ^ 70 +
        8318891424292054831898353624903680705523277393796719435905394543661594) * 10 ^ 70 +
        4626033326062164077620739149967947506344035888322760047766546503743305) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_128 :
    recurrence5Scalar1First.coeff 128 =
      -(((((11299511334431334885610366591083266756112185096846096875 * 10 ^ 70 +
        3355445716771878547906130781030824112070826419949132726161438042846603) * 10 ^ 70 +
        6917249294531487932876150789446493566615194544358134082182340092984794) * 10 ^ 70 +
        3666704819539060752781340219659107277477015874262306624049628796334086) * 10 ^ 70 +
        7368907852360391706044616949657716896171808658595853022518271102517394) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_129 :
    recurrence5Scalar1First.coeff 129 =
      (((((49283141899030274266274330776448027758182741001463373310 * 10 ^ 70 +
        6009917629767267957082825982555262607243905662351842938892677288460399) * 10 ^ 70 +
        9884151949006916004195958833186689379203223751130938707970594488831282) * 10 ^ 70 +
        9952913135830107596179144824134180354981251594088713018868562420192814) * 10 ^ 70 +
        9857588164006891127385813110298894458148447125908140053101290235900206) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_130 :
    recurrence5Scalar1First.coeff 130 =
      -(((((210355517785035782244264026003454146002256892908996318675 * 10 ^ 70 +
        8447691937371878683035207969466362887316199076165812612255700451597981) * 10 ^ 70 +
        3071143385134208343416207375025381773526847165521766947501769009283931) * 10 ^ 70 +
        6195382849281769255781784893931912664032129681471108975937457863420255) * 10 ^ 70 +
        6813237893844659676482087985848499922118098605939289711845454255745698) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_131 :
    recurrence5Scalar1First.coeff 131 =
      (((((878810280552032589748062025162386420602631693821297127656 * 10 ^ 70 +
        5918762436028241745954861413978041819632574385633449008287241474448487) * 10 ^ 70 +
        6782345720868034217996502772981272105349566350899393847978385912984737) * 10 ^ 70 +
        0615606770604162612767309264914735933152777151248266684156547105290966) * 10 ^ 70 +
        9362676996443878499681355781282396873753625581591187129873590294869239) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_132 :
    recurrence5Scalar1First.coeff 132 =
      -(((((3594090623512783949016618684460191011211534567456169747137 * 10 ^ 70 +
        5407436173919717294513974151911168810927827811095998977238077440687169) * 10 ^ 70 +
        2837816875138732735527752927656797583577389767837064070686483707898525) * 10 ^ 70 +
        6052079920356888782723583411752394202234425618200234065093953255893348) * 10 ^ 70 +
        2745145624901222743814259573453799216836880458802207847191393392684515) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_133 :
    recurrence5Scalar1First.coeff 133 =
      (((((14391322027640971674443932815613320540288087267329169236388 * 10 ^ 70 +
        8751910238116076854568480641750561986526863270511365824558111382541995) * 10 ^ 70 +
        0286430529305587427175889165870721930430476329335371151117057367868258) * 10 ^ 70 +
        4243828179084966120491070437846960227120920992669242645836340919359488) * 10 ^ 70 +
        6959236845679640216236273016730110185957752436893509100023272863833552) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_134 :
    recurrence5Scalar1First.coeff 134 =
      -(((((56427837171089268135357514825796118298678536154519181703650 * 10 ^ 70 +
        4384986305295581680903163138457513925015485918097129061602203890136580) * 10 ^ 70 +
        1404699264245863980976303020428350620229603543115527397387105931909410) * 10 ^ 70 +
        4927471744703523257007853659833026141074136126925931883523664518873188) * 10 ^ 70 +
        0308129073602122595306909097380268132185438311790775372380394316724064) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_135 :
    recurrence5Scalar1First.coeff 135 =
      (((((216684904283555666355927941591951445737861885798761046333313 * 10 ^ 70 +
        1583137158842492033196855413330163040056309696303189208102297781064528) * 10 ^ 70 +
        7219735576507939224583369972236139596264830270702459114688882161487393) * 10 ^ 70 +
        8847303274160571555928380307268077213910224873880145640807926166798936) * 10 ^ 70 +
        7465196568707853351029039765149322562591616408616759007095746970629077) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_136 :
    recurrence5Scalar1First.coeff 136 =
      -(((((815016138533989617020939651952553393655645141293832068161579 * 10 ^ 70 +
        4246604725955702853934528557285949438124682635834440938319011409770050) * 10 ^ 70 +
        8723932106567127363286049307266393430939349402416128819290993794096370) * 10 ^ 70 +
        3373019212538159624046833310510615021894687624608203644599117886735289) * 10 ^ 70 +
        6219195334043228866883095726940923910964822348702890569301756798607750) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_137 :
    recurrence5Scalar1First.coeff 137 =
      (((((3003060859467761171745545091066170546261557987870707380141789 * 10 ^ 70 +
        5392096043412303923135904248465395276249328869593469445830116143454661) * 10 ^ 70 +
        0317569024676141115350671137628788575821163517973770848772187093972568) * 10 ^ 70 +
        6189581558973236845971592461568478366511477830873267789044736186395385) * 10 ^ 70 +
        1507534816067693755375274703971213727371570797412365895388606216212479) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_138 :
    recurrence5Scalar1First.coeff 138 =
      -(((((10841237543220153331177212837649916429368643188484464971055359 * 10 ^ 70 +
        3791802504210206168026388913337060935050806206389598692868028280008241) * 10 ^ 70 +
        6915545465251867357443723116931934201666275466359232848643230166452586) * 10 ^ 70 +
        9428365766129909327355550885232956169124160963329326170263204999176353) * 10 ^ 70 +
        8494567364329824425151109747000960026526889073810064143440758661259312) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_139 :
    recurrence5Scalar1First.coeff 139 =
      (((((38349986406900856653874143569470088989189471594971120432402359 * 10 ^ 70 +
        1496937861438187759546929053774135305860552340089545326565616294437979) * 10 ^ 70 +
        0276694390913580408356423273070616636752345243969453151520209290416444) * 10 ^ 70 +
        2204398575600363512463435217293752449572863034684057604798280931271789) * 10 ^ 70 +
        8425423560110079471972565690785687177521051622903467916842046252813544) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_140 :
    recurrence5Scalar1First.coeff 140 =
      -(((((132946362243817375957154585389189973081926146191988121352328346 * 10 ^ 70 +
        8506849294606331938623074870497073921980123105753950852121515580665468) * 10 ^ 70 +
        3932917934727047442633687381643206593516705580137090400863609933690146) * 10 ^ 70 +
        1369758892962394425779549810375224589832371446778686269307593524587689) * 10 ^ 70 +
        8041099818222628227672339926855850021654583043553898598651675287454450) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_141 :
    recurrence5Scalar1First.coeff 141 =
      (((((451714812241042993826361097133995220741534735638799430395531532 * 10 ^ 70 +
        3564575720086337045684415263940748054706498270441379957778947434417948) * 10 ^ 70 +
        4362053607783302926218402557906064249654659655511323119508820387482228) * 10 ^ 70 +
        0393052814340077048559717375746913827925963178042288478194307600601014) * 10 ^ 70 +
        5117216852453000677709031414209674775980691122475459250544032871799770) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_142 :
    recurrence5Scalar1First.coeff 142 =
      -(((((1504454604146525562178884838822395686995908432680208810910800997 * 10 ^ 70 +
        7244953874985249270333845967157649342120990720012180679288082915313239) * 10 ^ 70 +
        4641083756872187032473544400765118996883591906306243428282730774189810) * 10 ^ 70 +
        0317218142800139383276772188794935061329205787644264094058224128939171) * 10 ^ 70 +
        7051303798519869008356428923186350368777702434022814242309870478364404) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_143 :
    recurrence5Scalar1First.coeff 143 =
      (((((4912126355947265727227052190715825434778921327947272717142118242 * 10 ^ 70 +
        6003118512616539143926916107583841482248472077788897578442561431065940) * 10 ^ 70 +
        9986641124293743213499424665349772830473612126514124139241250609184619) * 10 ^ 70 +
        9507458978809446694046883404426633754574428515020330181228078378535296) * 10 ^ 70 +
        2638925250888744197883723978663147536699966593261116817326886822633217) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_144 :
    recurrence5Scalar1First.coeff 144 =
      -(((((15724724549532022132916118370282504206606465001281149838490500949 * 10 ^ 70 +
        9235734227313404591046842955798986858010675440785888502071798609783988) * 10 ^ 70 +
        2941447737380837054059909060988579118038002054625434443746978194543611) * 10 ^ 70 +
        7052826292386165094626422523207487044706678634628096076699660616300498) * 10 ^ 70 +
        6813026819732933311358554462076932171189666868059955879140810878285537) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_145 :
    recurrence5Scalar1First.coeff 145 =
      (((((49358919732904860515409223982825430244198768752348234817072510648 * 10 ^ 70 +
        9416114821156955324182564070693441519079644239488404820424907662508958) * 10 ^ 70 +
        3717790329704198494640667002498473854754469753311846745907291119235062) * 10 ^ 70 +
        2697709995695421134416902071657998764075079770683679383265209969789182) * 10 ^ 70 +
        9438676932054630266586828178962757582438671354350424090183827522136755) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_146 :
    recurrence5Scalar1First.coeff 146 =
      -(((((151936454401947810303360538180126576250485528773057816210060737947 * 10 ^ 70 +
        8239537223361282706222594540083333651805080161315465878266449540562563) * 10 ^ 70 +
        2954081725155884651925733772826200640182383480399520252400290754982750) * 10 ^ 70 +
        1531255030339550301980574158518111394803028602664038475600891430847884) * 10 ^ 70 +
        7250080313320626800145033226299445852971567115507913973592686597793392) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_147 :
    recurrence5Scalar1First.coeff 147 =
      (((((458685922923966332039459837280227300468105928229641690927506144761 * 10 ^ 70 +
        2758893882168937480980998837262048209904900484832139193339510342194993) * 10 ^ 70 +
        7642358177933522570114404615468251584958952284640191014746066466164383) * 10 ^ 70 +
        4278544391237327670359277684708137745829382688418890154790000056850072) * 10 ^ 70 +
        7986521232014373559577576712879558445263503142791569955301279718827483) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_148 :
    recurrence5Scalar1First.coeff 148 =
      -(((((1358213279985123782293988889899015524796166128186789508106330047907 * 10 ^ 70 +
        9920647166040813155886873874893851497726101098748339535007912894439454) * 10 ^ 70 +
        8835998765488411365522394832385987299683328470617242193984347658452205) * 10 ^ 70 +
        7071227482799984102421636400472254739521276124994315551961621616246489) * 10 ^ 70 +
        6881947372259096494139657197861402065618749815503688166683591146029425) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_149 :
    recurrence5Scalar1First.coeff 149 =
      (((((3945122223911126722469154221528570405415571891411343684936107429752 * 10 ^ 70 +
        4707197020759384086134420707553390219275105303143257374030001006361760) * 10 ^ 70 +
        0882590260505140816102279295036545359858248327552587894563195635252238) * 10 ^ 70 +
        3711433511802988876552609586618497597059132977907302402188921216405844) * 10 ^ 70 +
        0973491756454572609665208812574369845919602908000278139919926575102394) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_150 :
    recurrence5Scalar1First.coeff 150 =
      -(((((11241711672304266960859001917478791976447276246804799003486794960269 * 10 ^ 70 +
        0920598727371283054379036481867232374068138500204700387129001430842137) * 10 ^ 70 +
        2595744497680725502622609280651662498017283706793947214291881777548925) * 10 ^ 70 +
        3264282526552990816612450476404489228445418994500871163091959303681363) * 10 ^ 70 +
        1740974197383316418786029633044736936894311565668943388062424186100837) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_151 :
    recurrence5Scalar1First.coeff 151 =
      (((((31428399391978415194701859269400283831051832698061624024504639523460 * 10 ^ 70 +
        9594765487688896633185562915865089191784389128671427931534109055421464) * 10 ^ 70 +
        6948412833925216832777343061188445729708493145697981126436756715983387) * 10 ^ 70 +
        2864017068446773374864840077864000079150164701814083878363048034361519) * 10 ^ 70 +
        1362964831477024270137589651083045904358133153351990617335701800319510) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_152 :
    recurrence5Scalar1First.coeff 152 =
      -(((((86211875712058195236708033698078720711709825435534435164990643578424 * 10 ^ 70 +
        7573684821167201817385781408879135428945836113728538657389057163214562) * 10 ^ 70 +
        2917401906581775599400096607320459314584668936674485082369312155081509) * 10 ^ 70 +
        1433378501369985525109878930034776946848319052622574568451382851788094) * 10 ^ 70 +
        0600623478358372055871754352696169092138956570843617249813359699191325) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

theorem recurrence5Scalar1First_coeff_153 :
    recurrence5Scalar1First.coeff 153 =
      (((((232061417145670779178501984962002324828475171393337103867866122060866 * 10 ^ 70 +
        3964021670246917761298611232831517373714605619488432687017793348033747) * 10 ^ 70 +
        1033589094206774742723878031138729087411418122531846583803863039992073) * 10 ^ 70 +
        4852780736016009376572668997222798102628205917571845659785787693661512) * 10 ^ 70 +
        2598037317405649997419211126076895251189696484583230604403171705680843) : ℚ) := by
  unfold recurrence5Scalar1First
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
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (154 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_154 :
    recurrence5Scalar1First.coeff 154 =
      -(((((613005915955283557561954133157781947827803601501690086586451618594614 * 10 ^ 70 +
        2334767098922771017958595080548725895471611632101573346402957620812055) * 10 ^ 70 +
        8723410780116562941647383909284841196075372541721770303076715840134440) * 10 ^ 70 +
        3918674237244398810682415938605076159068579038081269436360793244460046) * 10 ^ 70 +
        1935074159710019057235759907323495341612081195656649959147515613959661) : ℚ) := by
  unfold recurrence5Scalar1First
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
  rw [recurrence5Scalar1First_coeff_154_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (155 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_155 :
    recurrence5Scalar1First.coeff 155 =
      (((((1589227288153463517932631569137087387324646588844332456245365234274605 * 10 ^ 70 +
        6592502906936455492710305097287198506791500537263441223165170278310099) * 10 ^ 70 +
        4139405747764539205432520943745272889994548790066519240611892474853825) * 10 ^ 70 +
        4395831292134394738014430892355452880128776309810846624155766755577799) * 10 ^ 70 +
        7165323042872346921508923911871537685270376534813743444893305809583014) : ℚ) := by
  unfold recurrence5Scalar1First
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
  rw [recurrence5Scalar1First_coeff_155_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (156 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_156 :
    recurrence5Scalar1First.coeff 156 =
      -(((((4043892672570430983920187552402262574824847493427644682749209347770807 * 10 ^ 70 +
        6323529377943601516682107073288391900672616806595862452069354391443423) * 10 ^ 70 +
        5269474721420010280051424824926243683120724447189568582252273339958995) * 10 ^ 70 +
        6550242692539297577404742739774192076169989761890520854707722200004888) * 10 ^ 70 +
        2604106237212017680104235722702694489862776927358811478265052927383994) : ℚ) := by
  unfold recurrence5Scalar1First
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
  rw [recurrence5Scalar1First_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (157 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_157 :
    recurrence5Scalar1First.coeff 157 =
      ((((((1 * 10 ^ 70 +
        0100364217989582627168939552907650594830914299638370751643743762845758) * 10 ^ 70 +
        7788148923292200824233275411526183068955545053828772695568798652205886) * 10 ^ 70 +
        0104781632597241222747475201179647550314078107595723970728418711229375) * 10 ^ 70 +
        8685791829532528627144478324196133409410765199068164416114594275918449) * 10 ^ 70 +
        7398305789257237289579287955136813713697589027820483712550082759911696) : ℚ) := by
  unfold recurrence5Scalar1First
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
  rw [recurrence5Scalar1First_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (158 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_158 :
    recurrence5Scalar1First.coeff 158 =
      -((((((2 * 10 ^ 70 +
        4764452326510125592911003121420386535562480410225904065782750769267245) * 10 ^ 70 +
        2877161785379926735917723080008507483275436825038303590317440016988900) * 10 ^ 70 +
        2055402615084355882894407491130972593477821061703680785970316936158401) * 10 ^ 70 +
        7574709576977484336007234951759107031707487576023406932293545468778689) * 10 ^ 70 +
        1226544900099526429046741390696761393250240596115780307965145502959384) : ℚ) := by
  unfold recurrence5Scalar1First
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
  rw [recurrence5Scalar1First_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
