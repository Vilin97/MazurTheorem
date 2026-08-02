/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1First coefficient convolution

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

private theorem recurrence5Scalar1First_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (222 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_222 :
    recurrence5Scalar1First.coeff 222 =
      ((((((1089538532 * 10 ^ 70 +
        0167851081060886660054849966091423516507358935180955200254828036149119) * 10 ^ 70 +
        4223456665295661480342624417385491231068138871001475906904441266048049) * 10 ^ 70 +
        7023862492897884608091589299586261836703488713620659512227052329797083) * 10 ^ 70 +
        8781997177086395377063816935359337631001770200262879919110737447340987) * 10 ^ 70 +
        1000572052031211959111002780307229202440893673535232665425536916903136) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 95 = 26 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (223 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_223 :
    recurrence5Scalar1First.coeff 223 =
      -((((((1179439533 * 10 ^ 70 +
        1724681086922214908584558226205422876482965882615066295671701829046605) * 10 ^ 70 +
        6849407877007001112601023222918087100925995864193927077799883590299492) * 10 ^ 70 +
        2252102385242772944096281782704643354073653327935123858717353487973628) * 10 ^ 70 +
        7471098379745615431928241392540481902481702545241800893250423077891727) * 10 ^ 70 +
        0611363486669175028812727539554091979157541503518026748285198659248843) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 96 = 26 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (224 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_224 :
    recurrence5Scalar1First.coeff 224 =
      ((((((1189022805 * 10 ^ 70 +
        8523026176595504607435718699091752327704691005817056416678604848590148) * 10 ^ 70 +
        8120415043617467372077990473773348119826176093393879398272724848035564) * 10 ^ 70 +
        1501182083190939224760456219531599664098711418130262179488981832755875) * 10 ^ 70 +
        2023673786411842233844273960132417670471913278951596760531000408883312) * 10 ^ 70 +
        0324472436738002265112837819297957446898432378263418619326140153546117) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 97 = 26 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (225 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_225 :
    recurrence5Scalar1First.coeff 225 =
      -((((((1137314276 * 10 ^ 70 +
        8427529145803559556931602624466078820249407940192557112201108276309549) * 10 ^ 70 +
        5014576911651584707268998177999553497516836529742866285456940289660116) * 10 ^ 70 +
        5821852992690273751106338245122389207375477884926373172102820377281193) * 10 ^ 70 +
        9790826916509409553826039610264305832312340945162861357123904376993830) * 10 ^ 70 +
        3882473306881918044979600016348663172989943000499513557545747513508239) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 98 = 26 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (226 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_226 :
    recurrence5Scalar1First.coeff 226 =
      ((((((1042855050 * 10 ^ 70 +
        6953718786136237994346108018673600694611469629540347837565815777046896) * 10 ^ 70 +
        4017434132741914904649132121198745167117622611707972567877861793262883) * 10 ^ 70 +
        5793886978718667541490185552866117242824113672376385178767742014349187) * 10 ^ 70 +
        0817896531082091106163840061405643654705470412587411206858890731401033) * 10 ^ 70 +
        1803485507139238722898943697356031040869861848125660827533753754545515) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 99 = 26 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (227 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_227 :
    recurrence5Scalar1First.coeff 227 =
      -((((((922430370 * 10 ^ 70 +
        0901007018570577626597828565272814369676253604995236126852155592492485) * 10 ^ 70 +
        9702889682804385024845667294672576285067961488623452045661189855722939) * 10 ^ 70 +
        4005744664365749897377896091195276783572364561501320962770653971865116) * 10 ^ 70 +
        5641836418745003493722004701965394017388200264675106801085076507829432) * 10 ^ 70 +
        7578013538814567374908908207665069139803959039396027595213601441950854) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 100 = 26 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (228 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_228 :
    recurrence5Scalar1First.coeff 228 =
      ((((((790226376 * 10 ^ 70 +
        0296735195667260379860007358758624572808814439429282485022364253352517) * 10 ^ 70 +
        7190472519247800765864221261716186393031715522056929995291086589004265) * 10 ^ 70 +
        5748659506031792557134429437050612071691024313783723789792843622864044) * 10 ^ 70 +
        4148741828327981317546853168369049611586557183116505006134760459772199) * 10 ^ 70 +
        0738613836868695376760994063799294954332373897834247464550270472396038) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 101 = 26 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (229 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_229 :
    recurrence5Scalar1First.coeff 229 =
      -((((((657406396 * 10 ^ 70 +
        3140650287027290133099911984874426802735304781181281509433700468179490) * 10 ^ 70 +
        8265301714215981000619565297164388621375238242809906374708224206898190) * 10 ^ 70 +
        7086884198040062870609013441352732963206450444586594406536185900430944) * 10 ^ 70 +
        2355940340766209909548915307927339327081655480137420534844038973574544) * 10 ^ 70 +
        6680329120010942872714465512210548380588205892223579424089431933177159) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 102 = 26 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (230 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_230 :
    recurrence5Scalar1First.coeff 230 =
      ((((((532052606 * 10 ^ 70 +
        8745997742051228552714122559370126885082971031186402334584044887951650) * 10 ^ 70 +
        1773995938474975125152625814370395935519287190488301028842334162203196) * 10 ^ 70 +
        0321797341646362580763016840367014024586819998380343495072716301477263) * 10 ^ 70 +
        7599603714631738953848461338167180070140854534331128588369658196050815) * 10 ^ 70 +
        8838022343909119327827832137568978591070840468816190812444375394738935) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 103 = 26 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (231 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_231 :
    recurrence5Scalar1First.coeff 231 =
      -((((((419390229 * 10 ^ 70 +
        9777990732994921700598185429774961233937614161353033045911179212506546) * 10 ^ 70 +
        6400616896474193731368980956314965744218118475297721995686454274590886) * 10 ^ 70 +
        6478498355794679408617181169680937472088556750623631341901443132562499) * 10 ^ 70 +
        4977458733662421829373033605815092728237237276857821873017297016101147) * 10 ^ 70 +
        0474395368677021840593575147746855685491093362764995273648371839903560) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 104 = 26 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (232 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_232 :
    recurrence5Scalar1First.coeff 232 =
      ((((((322199997 * 10 ^ 70 +
        6935890580852879404964929220347422292554372883057938716589230395685739) * 10 ^ 70 +
        9819768052422732575544047269496578500668713144627736541598327822951451) * 10 ^ 70 +
        3955668055999566822577776234418232632295488758197365209524935710375686) * 10 ^ 70 +
        4853496074665819915663242350219433584818613611406322468274917358631418) * 10 ^ 70 +
        6907299479505615458912464023049275441436467391460958403185944567098637) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 105 = 26 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (233 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_233 :
    recurrence5Scalar1First.coeff 233 =
      -((((((241327823 * 10 ^ 70 +
        5320935851613790955782905104305545454730551356624036434668205927342877) * 10 ^ 70 +
        9548240879061696510297126117601638157452316813496690333323604318596904) * 10 ^ 70 +
        0281010656517568735683278365421060725992907993650760648591846153138611) * 10 ^ 70 +
        3924558576240362309966854172414204554205731488233756573880061457263532) * 10 ^ 70 +
        6407349142679302136534560411669627686434027210446463992752315183131866) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 106 = 26 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (234 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_234 :
    recurrence5Scalar1First.coeff 234 =
      ((((((176214321 * 10 ^ 70 +
        6459835288093272337936892497876193197322385054335381384860853434252968) * 10 ^ 70 +
        7149938384949448736263473261912087532763510882563673725637355172423414) * 10 ^ 70 +
        7818392160494688442809085405124115501547297317571874146163532487388309) * 10 ^ 70 +
        4728105697507794329462267401564139889983073938901076878431530814796030) * 10 ^ 70 +
        6249459528373757352688732135862424477530702876642554051053692459835835) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 107 = 26 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (235 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_235 :
    recurrence5Scalar1First.coeff 235 =
      -((((((125386330 * 10 ^ 70 +
        6682749910271792672592342077463520835085965781666516525948495683702882) * 10 ^ 70 +
        2651560079933424267781994837775070443083015066580326220360995408805966) * 10 ^ 70 +
        9556262392423629262209076902481554283880927350608292130225903827633012) * 10 ^ 70 +
        4122129636719533593102105079028959687051386477645271607027174790503993) * 10 ^ 70 +
        3187830780235106637462270665434524117027036193145745470729903904347545) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 108 = 26 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (236 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_236 :
    recurrence5Scalar1First.coeff 236 =
      ((((((86873672 * 10 ^ 70 +
        8521413071205469062148845141046122514972416148006776011415947375679183) * 10 ^ 70 +
        2814413129627157623483460871073948304879944463977126748262388343218376) * 10 ^ 70 +
        3146707271864264253817876400624819179607316405704873542510817524963693) * 10 ^ 70 +
        5587389786300197331225933771135451265672058516963925125284853459405877) * 10 ^ 70 +
        6520083241783092186772099100172187021219752924827993335145293328102423) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 109 = 26 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (237 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_237 :
    recurrence5Scalar1First.coeff 237 =
      -((((((58533717 * 10 ^ 70 +
        8943091520133569347419572881976922217867271923750336691546149862579386) * 10 ^ 70 +
        9558900808097947154134221761588632944906689981843418045833628002041041) * 10 ^ 70 +
        6501279579922355598994282056680102944675060761684981232623713993660103) * 10 ^ 70 +
        1132619196753033137627023521200830633007766295309184995504354083797171) * 10 ^ 70 +
        4546998774193776368973979139086149780676460923578052039674033193691821) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 110 = 26 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (238 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_238 :
    recurrence5Scalar1First.coeff 238 =
      ((((((38281854 * 10 ^ 70 +
        7824715376126713196454242230078310595679085456488955303400289210430790) * 10 ^ 70 +
        2401849416987034595841243786814331539731658412804805844509774404145809) * 10 ^ 70 +
        8610884027493773405025198502136077247792722565230117708179165030589822) * 10 ^ 70 +
        8764838772571976708976821759731333806779002882286390357622198926942569) * 10 ^ 70 +
        2280947463876718045732703355206355408412551397876095914448613144193510) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 111 = 26 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (239 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_239 :
    recurrence5Scalar1First.coeff 239 =
      -((((((24236819 * 10 ^ 70 +
        0981052114252335454853795541558777945033557827094169998469295798523382) * 10 ^ 70 +
        7507029307919752500133779801934449578054947220693394449551498507669887) * 10 ^ 70 +
        3370265507710833019394641799377973222094697955506716158937443866954443) * 10 ^ 70 +
        3133265094357549221053174110886510051944047732869205912031082505033650) * 10 ^ 70 +
        6282244973205282330424633263840658114224857971168750015149904606243937) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 112 = 26 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (240 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_240 :
    recurrence5Scalar1First.coeff 240 =
      ((((((14796049 * 10 ^ 70 +
        4651049463062901449358145944326425727867019514031783356393901330177336) * 10 ^ 70 +
        1966748032383497578887753482373766853413664007169107038491038012956062) * 10 ^ 70 +
        1073445899326443728871208444615502297476946484030578791810007190570918) * 10 ^ 70 +
        2294477636367570645870640161195221256123368259058355833600311820763916) * 10 ^ 70 +
        6331675671713309363242402660379330327136023413158618494055417166340349) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 113 = 26 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (241 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_241 :
    recurrence5Scalar1First.coeff 241 =
      -((((((8658566 * 10 ^ 70 +
        4390872513261155326168119269524638667184855178839330074689065082441563) * 10 ^ 70 +
        1922934345922171070547315297008871771689114478644743540075519314805529) * 10 ^ 70 +
        2465128055544184791695295052096571542866933919867230271204113110401453) * 10 ^ 70 +
        8262674352875967642712527194440630864256876219951910897640995203411720) * 10 ^ 70 +
        3837138523498138421673783815402985664270021570313129435286579712470381) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 114 = 26 +
      88 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (242 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_242 :
    recurrence5Scalar1First.coeff 242 =
      ((((((4812308 * 10 ^ 70 +
        7448072965528632974049265642440471772307851085267062952973365580214864) * 10 ^ 70 +
        8756191909685906561767632978318676370364603491829301076058103048244011) * 10 ^ 70 +
        3812151260009318352635781691147177233152052602337854908168694445897591) * 10 ^ 70 +
        8616029893348779578158451469601247545145620201891750128445406536220927) * 10 ^ 70 +
        7877381360960828483179312528798359670338909005559525333298282955569525) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 115 = 26 +
      89 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (243 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_243 :
    recurrence5Scalar1First.coeff 243 =
      -((((((2500505 * 10 ^ 70 +
        2898841743709452848109876316190051159567439066768019677624968376837499) * 10 ^ 70 +
        5343891097716898434509844617022786798908741593157680376314334516830521) * 10 ^ 70 +
        3546878020836207142106435339667677475054859233663378919511006506432647) * 10 ^ 70 +
        5839370158090069825513056225728093484629599831259971415416017789083773) * 10 ^ 70 +
        1252946298632691645285384080371655579716067501942854213668406343840417) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 116 = 26 +
      90 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (244 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_244 :
    recurrence5Scalar1First.coeff 244 =
      ((((((1178455 * 10 ^ 70 +
        5647771818349532728871427859219772170811468840794911136938353623827746) * 10 ^ 70 +
        0019655267371100943905681155974951615248999210357286016161132681699431) * 10 ^ 70 +
        4328976747573577555274096657130246577762234833728824771954052788125230) * 10 ^ 70 +
        6783314580561453707540754190778603475922203239560363937249201518891694) * 10 ^ 70 +
        1937181979266492164830060837548643277520171901863130953972128110972835) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 117 = 26 +
      91 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (245 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_245 :
    recurrence5Scalar1First.coeff 245 =
      -((((((468757 * 10 ^ 70 +
        5566048420321242386236133865375554315585036556314335308857690256030300) * 10 ^ 70 +
        2583308867219549034818742466497499242304563919602662712876996370112650) * 10 ^ 70 +
        0272782242198020448540055578177847784195707588109710311473315404168731) * 10 ^ 70 +
        6689645778614565503251721672637321625273813734566775930455624840898461) * 10 ^ 70 +
        6855973354246340312610135611350801951301286926639551780516403556007139) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 118 = 26 +
      92 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (246 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_246 :
    recurrence5Scalar1First.coeff 246 =
      ((((((120031 * 10 ^ 70 +
        6672091476978144412863056016968314979352171412417623207485636042757620) * 10 ^ 70 +
        3424435883820523005779179098645042336087683137919473078694041158498642) * 10 ^ 70 +
        3137263094323670364777853664510665857188818830358957868258625566512589) * 10 ^ 70 +
        4830676553399604506390484760670167191517631337744584131961578682764166) * 10 ^ 70 +
        9060480809140949232114856118008530988124800902951458298616590193168920) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 119 = 26 +
      93 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (247 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_247 :
    recurrence5Scalar1First.coeff 247 =
      ((((((28214 * 10 ^ 70 +
        1604408197045483825497254515908468215269581751306527348516062588194495) * 10 ^ 70 +
        2159204956012154525198365372660148187527225672923101420950084267278529) * 10 ^ 70 +
        1230560108682560822563900548220286823698860033405248255747223317742693) * 10 ^ 70 +
        6775612057162260409514717093302096755820495730522946216603507746982150) * 10 ^ 70 +
        3865362171168020406659584100656811259353055611868396988517188480445805) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 120 = 26 +
      94 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (248 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_248 :
    recurrence5Scalar1First.coeff 248 =
      -((((((73679 * 10 ^ 70 +
        0207270215359758092116658502937949318700960375674571890674229061377899) * 10 ^ 70 +
        1578347833056843644475113592534235335297995773903748382121914494276434) * 10 ^ 70 +
        3240879423126050096782616953274601764565168728953534234053687347333104) * 10 ^ 70 +
        4985708390755399121073045834665812041998014624947698430184994262243088) * 10 ^ 70 +
        0182237137872619417372699829545410206794005773008494679207234956942167) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 121 = 26 +
      95 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (249 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_249 :
    recurrence5Scalar1First.coeff 249 =
      ((((((72559 * 10 ^ 70 +
        4694106989266104933309929909428543910375620239632902835152299255517731) * 10 ^ 70 +
        9273260013116125084316462539419344385039602588994033943685579624902451) * 10 ^ 70 +
        9816651611312397988501446892801683754233729836657122769816229243439633) * 10 ^ 70 +
        9545628694750259921588364685009219185647593312029959380934877818174676) * 10 ^ 70 +
        5792592162469228602309731245214659766071244695376024099117950896077113) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 122 = 26 +
      96 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (250 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_250 :
    recurrence5Scalar1First.coeff 250 =
      -((((((54905 * 10 ^ 70 +
        4616648480163701704220134034932189057627360156292677266036585336286109) * 10 ^ 70 +
        9547782927424733768486515793555620492315360803619590539685328735704376) * 10 ^ 70 +
        1169045591633483442565476528082674515012772044116291173240103248766417) * 10 ^ 70 +
        0624635720030080343597854664386484246993312468614658064312179512641379) * 10 ^ 70 +
        5437471794220125821291954109519782564672655389611475260404644069143992) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 123 = 26 +
      97 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (251 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_251 :
    recurrence5Scalar1First.coeff 251 =
      ((((((35174 * 10 ^ 70 +
        1901725071692225300136058448613577475136574439613092969192350408227278) * 10 ^ 70 +
        3620386590211953823412952736772362522596159488391320592008491514957843) * 10 ^ 70 +
        5506814319840913295117022132091654972550057625701020445236814625361087) * 10 ^ 70 +
        3743236052354916141711109636704665387168302434646742305246180100939933) * 10 ^ 70 +
        2332272389494544617437043228527494142588924264390206244892995313306894) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 124 = 26 +
      98 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (252 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_252 :
    recurrence5Scalar1First.coeff 252 =
      -((((((19131 * 10 ^ 70 +
        2235533386491921634804366949867704019639601376796585492484656024380975) * 10 ^ 70 +
        0178960682929716573812791482940664883953806249345832010004953877700646) * 10 ^ 70 +
        6448486669727885491237516527227436269809255996875686488979187070578689) * 10 ^ 70 +
        3893674203212516154679005780916548523806420236465479343159987062447816) * 10 ^ 70 +
        4212711398464545736569735213655651908248625088365600059805688228086696) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 125 = 26 +
      99 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (253 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_253 :
    recurrence5Scalar1First.coeff 253 =
      ((((((8123 * 10 ^ 70 +
        8783066820375778038142734225922647779940280237275156494404015558539361) * 10 ^ 70 +
        5659881599934087272914959788887026181873065346424467111328148653405982) * 10 ^ 70 +
        8488952060686016816219175564686980127962855396014466453233717122821261) * 10 ^ 70 +
        3478531095144148153760990005898804011913602000612419563389993930375907) * 10 ^ 70 +
        4155805991549615555827406643067629259054433543693806528592405790008071) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 126 = 26 +
      100 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (254 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_254 :
    recurrence5Scalar1First.coeff 254 =
      -((((((1563 * 10 ^ 70 +
        5518624113906219394138154501946254908205551038755675491826501458132647) * 10 ^ 70 +
        1428073345860072274870194672155454376359530694062257331818658208720017) * 10 ^ 70 +
        2180241328491232705700038618269659381425312012328437881890962775724776) * 10 ^ 70 +
        9466057460226307162508891262204246979605756032372699675423490822208207) * 10 ^ 70 +
        2111357959450971678989074305225920731286028664252065320531592890531885) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 127 = 26 +
      101 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (255 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_255 :
    recurrence5Scalar1First.coeff 255 =
      -((((((1746 * 10 ^ 70 +
        2397897234893918139751787795553107008608628095600248463841045423182081) * 10 ^ 70 +
        3908336182529763460178363989829399804278306356553605675189880841976448) * 10 ^ 70 +
        7447276135474185850950725971772470484813039732794757602889510760381180) * 10 ^ 70 +
        0968980730801986227282236877987224701970041023560076759587795104701998) * 10 ^ 70 +
        6846419006819215878188152233130414274647896900345520025921981996515448) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 128 = 26 +
      102 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (256 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_256 :
    recurrence5Scalar1First.coeff 256 =
      ((((((2980 * 10 ^ 70 +
        8155081878873437029718311604060096195716695399962532353064458413054518) * 10 ^ 70 +
        0868888057173179190756808262400134237350732331585180020248641109982363) * 10 ^ 70 +
        5057891663543360830065536814108083838009220890307086313923353816851864) * 10 ^ 70 +
        9642495713375929230432482535819937202694314136758314853939555021867448) * 10 ^ 70 +
        4123852404343860469545305991674976547621655574760037867832210940957819) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 129 = 26 +
      103 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (257 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_257 :
    recurrence5Scalar1First.coeff 257 =
      -((((((3057 * 10 ^ 70 +
        7249936471129768356592849331026313947936891916073577765257982586305761) * 10 ^ 70 +
        5535523325318676438340341488643854972103900522884972702230237065498971) * 10 ^ 70 +
        8204822497228863471011929487268534962652414355781434926415873318457541) * 10 ^ 70 +
        3380502922573170150117032378022120892887742853380523979056823531176839) * 10 ^ 70 +
        1501854313746924270555895850803545954868995063879569319829962961528932) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 130 = 26 +
      104 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (258 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_258 :
    recurrence5Scalar1First.coeff 258 =
      ((((((2598 * 10 ^ 70 +
        8030185003419596194206023501609289721214136344124572055477639186832286) * 10 ^ 70 +
        2543916649872382944649807403566372502887033490430143168083160748544323) * 10 ^ 70 +
        4981288608451876199186570258589208973726959524760928074441475656668938) * 10 ^ 70 +
        6286242667259346570698539866838234655535973927547595955562546320111610) * 10 ^ 70 +
        0782868532559997739506658074096647073298212784168961903915642662761388) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 131 = 26 +
      105 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (259 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_259 :
    recurrence5Scalar1First.coeff 259 =
      -((((((1976 * 10 ^ 70 +
        8893129966292072786579957420170827273548572635940544810652986254008802) * 10 ^ 70 +
        2101049884639332889366324136764768084974111221152261304382146635063395) * 10 ^ 70 +
        7301136386422762109727015279683021707573597185104244681827984877993383) * 10 ^ 70 +
        8969924460986084909143557893516235226130031220984060973295845436147702) * 10 ^ 70 +
        9668206678652338484276963688244524519206019965813179028611265831870380) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 132 = 26 +
      106 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (260 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_260 :
    recurrence5Scalar1First.coeff 260 =
      ((((((1386 * 10 ^ 70 +
        0284637867955493373691308879942141065857029551665014721334384592892796) * 10 ^ 70 +
        8913331191816365870341647525789118396080434028036915510379387407601188) * 10 ^ 70 +
        6620086120346436696912169129620490574434675299054842404548695000605679) * 10 ^ 70 +
        3291663246073857555028464825477962554714667064665411318895904640303031) * 10 ^ 70 +
        7061301066145951202106493315855069409076641046711840423442152512863147) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 133 = 26 +
      107 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (261 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_261 :
    recurrence5Scalar1First.coeff 261 =
      -((((((906 * 10 ^ 70 +
        5044810550631522520769310040565689226833944111275707263888443797706590) * 10 ^ 70 +
        0977960476547078218224933523805703915957330063623198141730686669830590) * 10 ^ 70 +
        2294632274066666645530477744030109087261400096920328603178268623941740) * 10 ^ 70 +
        9711667914978306568788842538191799882039059273154961353149858039704084) * 10 ^ 70 +
        7340403841169586049933158708968894936579253561358080027014896145961441) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 134 = 26 +
      108 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (262 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_262 :
    recurrence5Scalar1First.coeff 262 =
      ((((((554 * 10 ^ 70 +
        4910931593438281787369448475884731926072689108095335177559035539752863) * 10 ^ 70 +
        5570693909232935873865072530138015138190215770740134450632693071546340) * 10 ^ 70 +
        3685790700240309720572140982765305922504231214214548383930196212394609) * 10 ^ 70 +
        4203947525538143300757887132302895302689715159747944422465443525904173) * 10 ^ 70 +
        3198922071749023631813735183885975383831796640161992794029609149633353) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 135 = 26 +
      109 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (263 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_263 :
    recurrence5Scalar1First.coeff 263 =
      -((((((315 * 10 ^ 70 +
        4007425342173642943946655827572036916026769529775579853621003081455861) * 10 ^ 70 +
        8787981160226912342551118744211143089949592218936964246511579082237672) * 10 ^ 70 +
        7698776090582670353505094076948566219873109206107324876643987836445447) * 10 ^ 70 +
        2838725369690540092615994225230567730444496480346113642139666333337917) * 10 ^ 70 +
        4058879559962607839375663151698007290676859793038670755743382625398614) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 136 = 26 +
      110 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (264 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_264 :
    recurrence5Scalar1First.coeff 264 =
      ((((((163 * 10 ^ 70 +
        8809799723117621287636296596674685256443834293348619581041250009360299) * 10 ^ 70 +
        2467616334961916145400130267238461235083070944821026284228525501157091) * 10 ^ 70 +
        9326305385812946517251417545317367450963841620084670441006832082286686) * 10 ^ 70 +
        7153460038851523796261116217702928630117503156313661198802711576749113) * 10 ^ 70 +
        5150041350082431242296960551458658143201756676437572945644845371996654) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 137 = 26 +
      111 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (265 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_265 :
    recurrence5Scalar1First.coeff 265 =
      -((((((74 * 10 ^ 70 +
        3474348944903146176846327434406364443281217189875197879387967267400714) * 10 ^ 70 +
        3405245944491951171379907893044304554534659340308752776551053893778152) * 10 ^ 70 +
        6103150740183036889231309042035641234407484134501375911661796443111491) * 10 ^ 70 +
        8963019640570463570946017737535491311042100547582135478556510297944291) * 10 ^ 70 +
        9379141532208734454584449671384496760004511504728740290727630630685296) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 138 = 26 +
      112 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (266 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_266 :
    recurrence5Scalar1First.coeff 266 =
      ((((((25 * 10 ^ 70 +
        5308691080733960460273775847450810937147558731403943093078607288306085) * 10 ^ 70 +
        5253865438810683565914197379548388899011612273859726463029408494960560) * 10 ^ 70 +
        8705312467392914123997233800509958972989225771166991894352045132396459) * 10 ^ 70 +
        4812842819148293698126770803948254643571114677762472237682696329197493) * 10 ^ 70 +
        3073798635878000590515941660654618789832358034998851083036170312237852) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 139 = 26 +
      113 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (267 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_267 :
    recurrence5Scalar1First.coeff 267 =
      -((((((1 * 10 ^ 70 +
        6480632511372597989080071597751336810612624778694311935635885150486174) * 10 ^ 70 +
        8195373193642144235857289407701256970219762474793061128358925038198492) * 10 ^ 70 +
        6275783916357738244999407151764785653550368207977634254169951648155915) * 10 ^ 70 +
        5231720674937999897134455820111178223580852839533221567625590627174924) * 10 ^ 70 +
        5544228812027751801276488934316636026016288121119549395409951072945866) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 140 = 26 +
      114 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (268 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_268 :
    recurrence5Scalar1First.coeff 268 =
      -((((((8 * 10 ^ 70 +
        0682975268240455320372153024771219567986335801787316574832689921353232) * 10 ^ 70 +
        7249177564541810115600280473849483400421250096218225990382693336769638) * 10 ^ 70 +
        8044223442839288413983400633683551265084191880721427328280426594609254) * 10 ^ 70 +
        8169735219450634104128736216440793048352917755012396581442715353840499) * 10 ^ 70 +
        0437968413219959849734027260421607491746531232838659737083950660102971) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 141 = 26 +
      115 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (269 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_269 :
    recurrence5Scalar1First.coeff 269 =
      ((((((10 * 10 ^ 70 +
        4461317308383473673067148737186241029188497798285612984083109759545902) * 10 ^ 70 +
        0277242264227383410931131838292769600659654630714596758279252147030434) * 10 ^ 70 +
        3717364465679989734754864570187190400818288788869476970722052060121509) * 10 ^ 70 +
        8455737816506275826777027462083363818366050792571341282207802783549639) * 10 ^ 70 +
        6453767979091384780230804347572242368387899323619785804170891365792119) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 142 = 26 +
      116 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (270 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_270 :
    recurrence5Scalar1First.coeff 270 =
      -((((((9 * 10 ^ 70 +
        5117922784283412696271520595230565420799000915638058866969650563398293) * 10 ^ 70 +
        3633958413153489016368283907765712326764837445846602831113041621303534) * 10 ^ 70 +
        5536931003699092643503255072104855948961706959434633517584572775343976) * 10 ^ 70 +
        9227500324895589695581900069072110972594693381920405158515919016636059) * 10 ^ 70 +
        1905614723518671273024128296475486416917740781225448679310468690160176) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 143 = 26 +
      117 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (271 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_271 :
    recurrence5Scalar1First.coeff 271 =
      ((((((7 * 10 ^ 70 +
        4506596669028499366059409910069757996703876020958572185385739690976241) * 10 ^ 70 +
        3571968890480867985844700587668997102430194484197518554274837702164108) * 10 ^ 70 +
        9461549563240818813885512526309999690056495100470788381053945316678675) * 10 ^ 70 +
        5269663910212238641507865677418466082560002156143851683311850111988750) * 10 ^ 70 +
        5904554411199787663516944355063629961531329017977863400890765201113496) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 144 = 26 +
      118 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (272 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_272 :
    recurrence5Scalar1First.coeff 272 =
      -((((((5 * 10 ^ 70 +
        3236524687959708495123748167532790768138753552961461225660417720213202) * 10 ^ 70 +
        7104350690117420386998224625633137566086571177804026412253989648162026) * 10 ^ 70 +
        7556465742980166847009094732143770487316290855922213902405929301194649) * 10 ^ 70 +
        2041038815969398064278118307585643309281989337320507756969523127628610) * 10 ^ 70 +
        3572569338948128023458636526452094989366089659563063578753783431579490) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 145 = 26 +
      119 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (273 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_273 :
    recurrence5Scalar1First.coeff 273 =
      ((((((3 * 10 ^ 70 +
        5561739290563321938891475242514128809776026437480450746327822580775638) * 10 ^ 70 +
        6053171339247633847071548749870963559357007856569151976080209941859387) * 10 ^ 70 +
        8405106194400362811745723575076268615718302188989898860041150959644704) * 10 ^ 70 +
        5739922149351216782625624228790878878017885481496181668606778512717090) * 10 ^ 70 +
        2093201069924478392294267604311763638542727090937801100172695264617887) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 146 = 26 +
      120 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (274 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_274 :
    recurrence5Scalar1First.coeff 274 =
      -((((((2 * 10 ^ 70 +
        2472985834777945667338673685836135340773676862577668379720464650347959) * 10 ^ 70 +
        2866766996612078965360562791052104840048851740278702515973392957076219) * 10 ^ 70 +
        5164483456770539428081692849569113312579592446068574973062560956899490) * 10 ^ 70 +
        3759703830611211936627875382056260746094076793654180247491907695088623) * 10 ^ 70 +
        1496408227180103289331131064812963320236273442900351764915443447893136) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 147 = 26 +
      121 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (275 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_275 :
    recurrence5Scalar1First.coeff 275 =
      ((((((1 * 10 ^ 70 +
        3510814767176050819018645542162063497467566367291257447240409031069397) * 10 ^ 70 +
        6010752210267479397097585293507636847467875350857703230409852368345703) * 10 ^ 70 +
        5763190045153044594750319597303381520497476470960247774398989939346455) * 10 ^ 70 +
        8953258404083008571965509143240555242807939865140726306097374963004642) * 10 ^ 70 +
        9436726622527881525653329569130943593918222145243242700398350686083290) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 148 = 26 +
      122 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (276 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_276 :
    recurrence5Scalar1First.coeff 276 =
      -(((((7740769800277456485867849302223599125979326650204768452502041463505976 * 10 ^ 70 +
        2736254962098334353704618228409393638922980458009680587970146057674021) * 10 ^ 70 +
        2271270488423134993129343473938220281624772167114721370586501263984681) * 10 ^ 70 +
        8837752813051820236418338577885013985438444264359885984787379448969574) * 10 ^ 70 +
        0781071465310457378992707875483179998084045763202375217488980673297053) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 149 = 26 +
      123 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (277 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_277 :
    recurrence5Scalar1First.coeff 277 =
      (((((4219634400492828831969752382830373858254419290834954749029070003113962 * 10 ^ 70 +
        9012455915692650615275542062235144260876892917636860080348296884644723) * 10 ^ 70 +
        3660607626634524470169386542892725825024844144825157699316667163211134) * 10 ^ 70 +
        5241502620741821112975042249705757764186318510344831554318384464036259) * 10 ^ 70 +
        3487747689266348268314630456225342646190264069144067712276063888725600) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 150 = 26 +
      124 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (278 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_278 :
    recurrence5Scalar1First.coeff 278 =
      -(((((2176600581581036023802779390711770692537549032686645297605193179242572 * 10 ^ 70 +
        5790374152450547506548718951078324806860489608309490310830600838645788) * 10 ^ 70 +
        1452535697909417877809419766464660603538035237602120789304262858177471) * 10 ^ 70 +
        5114049773770903746489831526822474046380098858727118269831818114902787) * 10 ^ 70 +
        6380181116995697011527605587379762310181065404768308268546440398723870) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 151 = 26 +
      125 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (279 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_279 :
    recurrence5Scalar1First.coeff 279 =
      (((((1050169344396331244028219584251391770987807397508342542241074000822382 * 10 ^ 70 +
        6111629345974542774024492760637665991876085735538160333577159073903793) * 10 ^ 70 +
        8834247092471760277415242791514547192664227834218980371309062413684081) * 10 ^ 70 +
        6558704910908600132130317787332663300177001697162319162009970074587971) * 10 ^ 70 +
        7102833359647792256400088447027202324258538370343671744489017791076556) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 152 = 26 +
      126 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (280 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_280 :
    recurrence5Scalar1First.coeff 280 =
      -(((((462655570746407064608184196741154717492849546569799506362132795798018 * 10 ^ 70 +
        4944648130268917333213517068224665786545423804421219823565999607656179) * 10 ^ 70 +
        0131675919501639587912143260434441490872539430382606015073272125051572) * 10 ^ 70 +
        4437467753107147078063869730417048655635265882005605361459965260356091) * 10 ^ 70 +
        1846384520327645714042953397703704619994828431796143873835509880720596) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 153 = 26 +
      127 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (281 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_281 :
    recurrence5Scalar1First.coeff 281 =
      (((((175737462659839915135449203258423239751480010428614499665526289716355 * 10 ^ 70 +
        9800293772107434012258332112649535472784095471016497795004650300943232) * 10 ^ 70 +
        6414665755043226514432905186210997604433144268757302915487000113107322) * 10 ^ 70 +
        1767398930605350534366419047143422120954616828884301147596784614634208) * 10 ^ 70 +
        3759591442065959506129775986665506380459898149983938363782440534639931) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 154 = 26 +
      128 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (282 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_282 :
    recurrence5Scalar1First.coeff 282 =
      -(((((47327210445845912078551648481733670912785442818487796237570711905813 * 10 ^ 70 +
        9365193524859557185955633493506574250147820132302704928739452734278910) * 10 ^ 70 +
        8126497445964545690018509367515318178142266607265759642911204957552595) * 10 ^ 70 +
        7765603026915257703578502808698040388826937468546888160003187715820760) * 10 ^ 70 +
        7183892159487363306629642629077456040005959821855464856732203654055368) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 155 = 26 +
      129 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (283 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_283 :
    recurrence5Scalar1First.coeff 283 =
      -(((((2773560940569786322601692631057550293922588407242048579323056721255 * 10 ^ 70 +
        7568528424257644704052177556393479009215492383116428251064233002714059) * 10 ^ 70 +
        3735335489922136859467730537055481674019741878155779082122078263957313) * 10 ^ 70 +
        2805108137727905417306267566088473946171085602350569967234740836125661) * 10 ^ 70 +
        9886454777875116892256166479028137401735303402013865930463134610698373) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 156 = 26 +
      130 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (284 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_284 :
    recurrence5Scalar1First.coeff 284 =
      (((((17316385557218606163396613163872373266362971068775753282134585368840 * 10 ^ 70 +
        4844979803938499510729091701088627810597154213835369167456753172672807) * 10 ^ 70 +
        9243932807724439563607060527996545421261121951914364335451995451415522) * 10 ^ 70 +
        7179979863530201360218906538680814446004037851482093691306737318412212) * 10 ^ 70 +
        0421485465651457638097868982583734480040466352047834475779744931550502) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 157 = 26 +
      131 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (285 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_285 :
    recurrence5Scalar1First.coeff 285 =
      -(((((17657808318097295634171397548621630819138583069578295242190668175787 * 10 ^ 70 +
        8474997346658218035843847130571362839878634060367775152837472213017220) * 10 ^ 70 +
        0689203106158459739035670856053727021230033971330917108499945789105149) * 10 ^ 70 +
        8935904636211091402380691842247759865771883610294022552489581664954261) * 10 ^ 70 +
        7021735401610005611533221028057482970936210134334900244921416690381669) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 158 = 26 +
      132 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (286 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_286 :
    recurrence5Scalar1First.coeff 286 =
      (((((13625331094129830411683613769513111235571187347920861626232080624351 * 10 ^ 70 +
        6100657806534076342680343309691430152401619012815282712703236225494018) * 10 ^ 70 +
        4849087165436350970483070918994237191142548889042468579114525337135320) * 10 ^ 70 +
        6651684397852626024682136358882808246728116204615565754433220742854425) * 10 ^ 70 +
        6755420504768405235154021891381465357587585009899559228126556943826332) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 159 = 26 +
      133 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (287 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_287 :
    recurrence5Scalar1First.coeff 287 =
      -(((((9225421046875785621022205865128623520762424462867693123055375996619 * 10 ^ 70 +
        1481014933404517981347224799800507226610252535245481406476451342073313) * 10 ^ 70 +
        0561319768227606183773170774314375365304609914075088922442372150589609) * 10 ^ 70 +
        0449940218962945651308902561527079456988397427390990388222771660217308) * 10 ^ 70 +
        5668181058323356116337400830755737699973129372914155557069525014950759) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 160 = 26 +
      134 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (288 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_288 :
    recurrence5Scalar1First.coeff 288 =
      (((((5752694601979629088674216209731918775064105063576027276590152477903 * 10 ^ 70 +
        1748053923153642376658338388480893337847958061107446147570011070917120) * 10 ^ 70 +
        3989566637155306322320791442229063810864935213668618576631669618864821) * 10 ^ 70 +
        9970937234294091239073288865803842798826790440070743044292348430659541) * 10 ^ 70 +
        9013719846249810037751733325900903138618664565427114019614132532131802) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 161 = 26 +
      135 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (289 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_289 :
    recurrence5Scalar1First.coeff 289 =
      -(((((3375923608488736617019541915048765954687131486076284008216301827440 * 10 ^ 70 +
        1105429469212210124101168596668053689121153838113141827809273662027858) * 10 ^ 70 +
        6129146818225645093330745463619667938073451758776481899889797368096194) * 10 ^ 70 +
        0742002748197574825035966511095694844688039836800776343554987503837344) * 10 ^ 70 +
        1610827086398956667536129205960848418710573240862115671996776596369628) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 162 = 26 +
      136 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (290 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_290 :
    recurrence5Scalar1First.coeff 290 =
      (((((1885390806691816614227439914426351897046219087644643302157532841977 * 10 ^ 70 +
        3914092610210430412467098003948278808675499976748551230898028989737833) * 10 ^ 70 +
        2522787446553874759040492302897086907424534126351220722417405288934453) * 10 ^ 70 +
        0127158515613820699001073032858114394784710387302848061382770836344662) * 10 ^ 70 +
        3223389041331132579553883646815270314395982768079315990978251350586840) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 163 = 26 +
      137 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (291 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_291 :
    recurrence5Scalar1First.coeff 291 =
      -(((((1008210386247360411946589492566502483002738379533837465764121901008 * 10 ^ 70 +
        8087147149243678309603149629497081065050106898880029052831289726568550) * 10 ^ 70 +
        2784275124834376229033397623767641980981404999614271702756585882869867) * 10 ^ 70 +
        8513149547589718870665136024170537542978885545208439015839043913494560) * 10 ^ 70 +
        9164008541258159917031471728846058041979774255537332428521842175495110) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 164 = 26 +
      138 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (292 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_292 :
    recurrence5Scalar1First.coeff 292 =
      (((((517904150117437402835308280255740953683790298779142073642004025709 * 10 ^ 70 +
        9526293157992852949939688236313870258961376563370051621727698934366397) * 10 ^ 70 +
        7222923029398482678838164488708149829022701500252223700115565312345250) * 10 ^ 70 +
        9741482357629043898559495957860675358873187428984086819649164447078316) * 10 ^ 70 +
        9114466144899713841805112396309648223636009547335067854969892840203673) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 165 = 26 +
      139 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (293 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_293 :
    recurrence5Scalar1First.coeff 293 =
      -(((((255914262982288498612873252913585251899534024403555042245638157733 * 10 ^ 70 +
        5441825324523719480612779016534745936002658530828396788901096794918245) * 10 ^ 70 +
        2207952542984290344879869367542324803805083593891656724038534963576563) * 10 ^ 70 +
        3343389471249383364018658232406726717600592132159193905084106897248432) * 10 ^ 70 +
        3318415235599427852703935821482931810944883711656339103997186954780430) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 166 = 26 +
      140 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (294 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_294 :
    recurrence5Scalar1First.coeff 294 =
      (((((121643594184120117559536517919036024018922546500388853823820266093 * 10 ^ 70 +
        3194007397804903105087726819800285618585879390084442588345037296198658) * 10 ^ 70 +
        2126958396950286892144700449621065040253008683679400718817920243674064) * 10 ^ 70 +
        8072752925736840456371766002986726527298876903374483458662589295759177) * 10 ^ 70 +
        0307955652762286204006577945554260642990746419941999975050538291576979) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 167 = 26 +
      141 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (295 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_295 :
    recurrence5Scalar1First.coeff 295 =
      -(((((55557850700579332477029222853893855926318157284547533881434176205 * 10 ^ 70 +
        0661988953236835354884378381086399818922325003059770915612149127850146) * 10 ^ 70 +
        2738258464126068881311019462804486772677219958190672739270958358887249) * 10 ^ 70 +
        8198625451611487795512098333594492786127403160212659921891829340858715) * 10 ^ 70 +
        9924350172881938052979562196908804089034919816449639349947633513228580) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 168 = 26 +
      142 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (296 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_296 :
    recurrence5Scalar1First.coeff 296 =
      (((((24329663665663050952741040222240776217608766249873129374296419159 * 10 ^ 70 +
        0174414786672821170489724158811867421618547636832080324641652430492823) * 10 ^ 70 +
        8705914457465713739681300449733245169040685759179733176479610118319332) * 10 ^ 70 +
        7843076669436026574780276332587257732375404028315076583768437979234556) * 10 ^ 70 +
        8729897220660141878365578780284018713843312224772708011804536797806031) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 169 = 26 +
      143 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (297 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_297 :
    recurrence5Scalar1First.coeff 297 =
      -(((((10184515191334288848408604035155561733457921138994324518201029637 * 10 ^ 70 +
        5087183963599583437414874685208839094300317645744429160223564047645144) * 10 ^ 70 +
        0394518399437101327324210339464803036427081624211401501889995670648228) * 10 ^ 70 +
        5684797150031140831372545389330022510595280626055644861928113212467216) * 10 ^ 70 +
        6905305180826072897746774742395527146867693359502962743289808518718770) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 170 = 26 +
      144 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (298 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_298 :
    recurrence5Scalar1First.coeff 298 =
      (((((4060285394089823063698990116464904648590154750723686555168558509 * 10 ^ 70 +
        2572430165536027004029815055248253232396577293770842103572351281580884) * 10 ^ 70 +
        7041349932123249048361271928208518086097957606709541634758149723948333) * 10 ^ 70 +
        3652577677207183389600469179026681889997044194941908573295196812366328) * 10 ^ 70 +
        0246440862295772422066836753092212145443845278697141874966890559486788) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 171 = 26 +
      145 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (299 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_299 :
    recurrence5Scalar1First.coeff 299 =
      -(((((1536294040013735336608247972427037965861523590119877197371030173 * 10 ^ 70 +
        0030747926700752116087201228741972620704153359616455947143708950450938) * 10 ^ 70 +
        5676884517546784809575134693861362024961083962814449382372166270276574) * 10 ^ 70 +
        6728031122209412232693508573325523763313644004009546315728936986373379) * 10 ^ 70 +
        9236473233992238192061013245517301681726248084101439316064997294102747) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 172 = 26 +
      146 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (300 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_300 :
    recurrence5Scalar1First.coeff 300 =
      (((((551349517790870357514372255948973997106055157505717316846304885 * 10 ^ 70 +
        5187839453090341293364580300032764688202583662290425244450397815734729) * 10 ^ 70 +
        0607285220655539358851255872317693221237834282945522092386199758908795) * 10 ^ 70 +
        8767159120353605803283367457054542129118918733133616679586886085837253) * 10 ^ 70 +
        8204190915395675584405169978507595606778383602846762537570759508331636) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 173 = 26 +
      147 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (301 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_301 :
    recurrence5Scalar1First.coeff 301 =
      -(((((189524432749377838810470646540463588314496048865604202923369270 * 10 ^ 70 +
        4207006759798201302018769165388314977737041852422547583230282586352373) * 10 ^ 70 +
        5096955576506602673272311676633864182415009917988729551495429273260295) * 10 ^ 70 +
        6723642429073865869895502897737924811416437482777566731483011424158849) * 10 ^ 70 +
        0770748697733111722650764912549210412463000088990121529279186243031558) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 174 = 26 +
      148 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (302 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_302 :
    recurrence5Scalar1First.coeff 302 =
      (((((64829007181024848765609473500793407430169546034159349770023070 * 10 ^ 70 +
        1155925580163055991373286958570109415767405159120689549065446146351941) * 10 ^ 70 +
        8766430424022803966977865139857963305863597508762002967005232529827084) * 10 ^ 70 +
        2092943034791374271461424401679414052293970070824351239131833126571951) * 10 ^ 70 +
        5814266858868663862495603288198004840150518303961043685012063095897951) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 175 = 26 +
      149 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (303 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_303 :
    recurrence5Scalar1First.coeff 303 =
      -(((((24150719301256381337547215550491197103534158446728263290930088 * 10 ^ 70 +
        6936046321124664573509665804980243960586178240692880260405949614335332) * 10 ^ 70 +
        0581699656826678368724103976400507401012112333109466105382489490567402) * 10 ^ 70 +
        3444782239981115343195531499002998133839382247905775556890603103883127) * 10 ^ 70 +
        7450691783958914397480079586880924349072864971847077331920101637091751) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 176 = 26 +
      150 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (304 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_304 :
    recurrence5Scalar1First.coeff 304 =
      (((((10941898409697845289188803047931837966030247803783435187908703 * 10 ^ 70 +
        4871967696943177868055623127480779425663908134753549028056217819274004) * 10 ^ 70 +
        2252205907930220512926687311199606674907086236413951608096047968803283) * 10 ^ 70 +
        6891805918638493820051106646628335926740051147810848012783868192495709) * 10 ^ 70 +
        2413478233277406140377343911086059133198198440414522301810375197329821) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 177 = 26 +
      151 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (305 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_305 :
    recurrence5Scalar1First.coeff 305 =
      -(((((6058052333445661229622517345490001794241211443721592864150051 * 10 ^ 70 +
        2430042598603115627635472949602705508814288248081603028979365085720746) * 10 ^ 70 +
        7354884401600615172107866505484129432258693345338639815714351492682709) * 10 ^ 70 +
        1087380256347217780646050690985332721736200247142090199236525628462770) * 10 ^ 70 +
        2915471172015188395647676436106187118806110689215594306012890163096462) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 178 = 26 +
      152 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (306 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_306 :
    recurrence5Scalar1First.coeff 306 =
      (((((3674394964539552161854665818387417817454640578934011646149567 * 10 ^ 70 +
        2059419496170159774170291387257269339554691677337241040657593661962139) * 10 ^ 70 +
        1967710866955255074063796519867960312087912172290877982060257757207839) * 10 ^ 70 +
        0698610325630933622052461403163967019522854143454385025348817799694238) * 10 ^ 70 +
        8284192923829888104734322350022073586000430942216589413738409805064600) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 179 = 26 +
      153 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (307 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_307 :
    recurrence5Scalar1First.coeff 307 =
      -(((((2216016342721492286148499938951880532623286611248570037412814 * 10 ^ 70 +
        1916114288137712704748382654836283623203085055375085799181525084123435) * 10 ^ 70 +
        8536018913065704519686494634855216281153866926409315680669596291198109) * 10 ^ 70 +
        6412707810327060769701347030473525816900982537728520087690442890704463) * 10 ^ 70 +
        1865486721394722766500288203362462429772076058083600034220219011998805) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 180 = 26 +
      154 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (308 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_308 :
    recurrence5Scalar1First.coeff 308 =
      (((((1271246022074694327775412624947320516196419862139879265861559 * 10 ^ 70 +
        1023572738138300152399145288074408243349901776690264084949769481693715) * 10 ^ 70 +
        6447223596966020310266806993300668941507274672062420206023996598534421) * 10 ^ 70 +
        9674390246110358006959049879077700375554318319565414503196685409351116) * 10 ^ 70 +
        4858590307589760485046508870066407564553035259811805916718435802791801) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 181 = 26 +
      155 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (309 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_309 :
    recurrence5Scalar1First.coeff 309 =
      -(((((683577905786614415730456995200797386255294869944214060447787 * 10 ^ 70 +
        3029585434328325934561655334012919446244891475104609117837280270593820) * 10 ^ 70 +
        1807614194762823129292809875209089419055305753840209642145248270054173) * 10 ^ 70 +
        2392220261686917026862246795339742987375033279006602110620337666262082) * 10 ^ 70 +
        4774209796418836949852898775910767157195660656893985236860509880231791) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 182 = 26 +
      156 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (310 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_310 :
    recurrence5Scalar1First.coeff 310 =
      (((((343030583654507366751306336297551662122496273521592225336593 * 10 ^ 70 +
        6524709995616175380199676879560235703931508633802544037855480834334227) * 10 ^ 70 +
        6865990170550395851016247311547840743346583613739120124172332030986852) * 10 ^ 70 +
        6329935968330042600365020340252152590533779912143165804784539231263663) * 10 ^ 70 +
        8506958203188450775394194954759288327771122063927446050057058018890189) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 311 = 1 +
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
    rw [show 182 = 25 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (311 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_311 :
    recurrence5Scalar1First.coeff 311 =
      -(((((160134264002829378947997325308560260658379059117857128005438 * 10 ^ 70 +
        4157426354335773597060305960705832086007316820024189845173886541299994) * 10 ^ 70 +
        7695674400068079256220060262996964461102573164864221647079195054882124) * 10 ^ 70 +
        9500422066091740882820887182416882704379478811695842533174194905747024) * 10 ^ 70 +
        9430326255295711774207551825276717633429905689891007075646793692966703) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 312 = 2 +
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
    rw [show 182 = 24 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (312 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_312 :
    recurrence5Scalar1First.coeff 312 =
      (((((69079247473852752138351586682845738997060386193469721976387 * 10 ^ 70 +
        5778709084931343101872569048265105891803911944653943222913493171575404) * 10 ^ 70 +
        6514283793592969886963680451584621374854110338707276742056537388598431) * 10 ^ 70 +
        0267199815886923211672663435540674196650905228511330499086800214211010) * 10 ^ 70 +
        8189722854942155437997103267967817250368940109693300210295124599683792) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 313 = 3 +
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
    rw [show 182 = 23 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (313 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_313 :
    recurrence5Scalar1First.coeff 313 =
      -(((((27115505359945359015626655499972480965695423111871542294542 * 10 ^ 70 +
        1272378148438607922235656404794158709376617409389308433626950305105634) * 10 ^ 70 +
        0014552962899440751169366252371217858632486365573456860375393918509229) * 10 ^ 70 +
        0839069573597509583920011663613793771677242511494859882810359024590790) * 10 ^ 70 +
        9090729430909335382276913151735956235351559089773522196291692415918634) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 4 +
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
  rw [recurrence5Scalar1First_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (314 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_314 :
    recurrence5Scalar1First.coeff 314 =
      (((((9333001973586099895456632487862623710826499896443011414346 * 10 ^ 70 +
        9089255511860709169931982074500962679302645434246899140827647378958594) * 10 ^ 70 +
        5620498030914297864270910187625942296803661393213802482244511209245514) * 10 ^ 70 +
        6932710507614736788718604731045236312931825844927024743941729180610537) * 10 ^ 70 +
        4224454250507934616542756328775720219557628288956808350460876022211379) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 5 +
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
    rw [show 182 = 21 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (315 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_315 :
    recurrence5Scalar1First.coeff 315 =
      -(((((2525968983043127022998964497814959505398642210138886965468 * 10 ^ 70 +
        8929191423911683763886765985535266202574907435538447503299435873406325) * 10 ^ 70 +
        5667071181590365106660212626147172846518247586660022411144169871400242) * 10 ^ 70 +
        7209885605918703922380322266701536267111486357194078091704001354963677) * 10 ^ 70 +
        7659985461712267502826836128355615475430685676521587036837505420929181) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 6 +
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
    rw [show 182 = 20 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (316 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_316 :
    recurrence5Scalar1First.coeff 316 =
      (((((275724165867763396929646829214302048146541722963171077479 * 10 ^ 70 +
        0090100302312866946200552645339791865642319542263603280308976872907700) * 10 ^ 70 +
        4060102059441467361659465016380972983836578034610259700449572167068820) * 10 ^ 70 +
        4077093947402522738445239126356767117377204600339384028410995335355533) * 10 ^ 70 +
        0053058960687116602696560680573167594063632681087554653454902289290246) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 7 +
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
    rw [show 182 = 19 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (317 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_317 :
    recurrence5Scalar1First.coeff 317 =
      (((((279871210892504894961547627070934590377059085080930175252 * 10 ^ 70 +
        2611303093021181515708245894729820828010120572455120391164875950069759) * 10 ^ 70 +
        0009121767771955700977105257982224368223773890593330931889521361434386) * 10 ^ 70 +
        3025261528555449569869069139426578687370805152021700570641527423509215) * 10 ^ 70 +
        8867930723543745048131836888422605732509432399590366369104492712851188) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 8 +
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
    rw [show 182 = 18 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (318 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_318 :
    recurrence5Scalar1First.coeff 318 =
      -(((((301717084635880083114515995650004941110060630973339665872 * 10 ^ 70 +
        2676555358514044280351150955691488526636416221964418718723887666222954) * 10 ^ 70 +
        8701533419724880241866288028334923798788914496982451405060813558666043) * 10 ^ 70 +
        6839804464521504235948518945627459960177049811890633470245066986032642) * 10 ^ 70 +
        1312430224216914933136084057983854246599224494407944267957911771695821) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 9 +
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
    rw [show 182 = 17 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (319 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_319 :
    recurrence5Scalar1First.coeff 319 =
      (((((207365504784892349084661296099611839064776163905154767317 * 10 ^ 70 +
        4058588311033991775490148318522550547358807157100232695355630784653283) * 10 ^ 70 +
        0373608828090694030245558194902395992811369794313960191295383267897564) * 10 ^ 70 +
        2973181639544271335665964673019781438649790405213081358410891575324427) * 10 ^ 70 +
        2670783076025521540497531876884474808780784323660042002860130332266183) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 10 +
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
    rw [show 182 = 16 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (320 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_320 :
    recurrence5Scalar1First.coeff 320 =
      -(((((120763665885219217538753317393013412214762068741157187718 * 10 ^ 70 +
        5097536887850522439231182954887163848115883380444531803739683938041036) * 10 ^ 70 +
        6073906302848219231904517449098492948835869849703565008418257957373400) * 10 ^ 70 +
        4469877434708482180448123939635135297235626050791096323771450622911619) * 10 ^ 70 +
        4708981466646745594138183540833003392416469776342540362716302287885226) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 11 +
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
    rw [show 182 = 15 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (321 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_321 :
    recurrence5Scalar1First.coeff 321 =
      (((((64292234060296693753188898936449204194693478839882663928 * 10 ^ 70 +
        5750859614339540159753378752684892507321492653737490666869698237104632) * 10 ^ 70 +
        8585608261435606672376337064836794445081988297503569074371643126870973) * 10 ^ 70 +
        8402375557480877617127288043556605056434978112559360255528361292974921) * 10 ^ 70 +
        7848660040624082079444158375793683906779041690577615886852976682778122) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 12 +
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
    rw [show 182 = 14 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (322 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_322 :
    recurrence5Scalar1First.coeff 322 =
      -(((((32353861560458656018569093949393123480466828214908968894 * 10 ^ 70 +
        7355487733880426263203920769604445226241707231849681663333988014024228) * 10 ^ 70 +
        9710693649159292245614047835647508567426521222408200333968580411821416) * 10 ^ 70 +
        8333582989749845439663573771789571477041321138560528162209166707786652) * 10 ^ 70 +
        3742283018596949549176072133268842526808191605259588130439992350057395) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 13 +
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
    rw [show 182 = 13 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (323 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_323 :
    recurrence5Scalar1First.coeff 323 =
      (((((15681986732591020541227643712721765569337104309806814168 * 10 ^ 70 +
        9177303264204326685783195697565177263254834118884510056562031199721683) * 10 ^ 70 +
        9709040762535034921082647993856234553682639010170696165125997078940541) * 10 ^ 70 +
        9670789562725765256981564692519870593136154137731864760306363608496687) * 10 ^ 70 +
        6263154793652215602160197251914424338832053201487422304948181422900492) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 14 +
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
    rw [show 182 = 12 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (324 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_324 :
    recurrence5Scalar1First.coeff 324 =
      -(((((7409859255552543690807680786627975724869237762147511204 * 10 ^ 70 +
        0130789975216925112619200252500063546694039354714512625294889868869317) * 10 ^ 70 +
        1788566393797536691563209817594104674508742071137653544245584568562626) * 10 ^ 70 +
        7351462105061111981741672411087721087608504403024504389383188760835115) * 10 ^ 70 +
        0491981525024079274397356955511641819315657686028984443383204754156154) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 15 +
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
    rw [show 182 = 11 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (325 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_325 :
    recurrence5Scalar1First.coeff 325 =
      (((((3440721498987501634776724425036167887897350500683931453 * 10 ^ 70 +
        0950603726229333953346552741174050146386726852669487937876503035840534) * 10 ^ 70 +
        4785006767551642783880439295785465668005870555080805980998696250442823) * 10 ^ 70 +
        6455753570785328591452034621518253079722725933618869215303740872191218) * 10 ^ 70 +
        0215550872025206327614428468066399051824653434003149035615271770955136) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 16 +
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
    rw [show 182 = 10 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (326 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_326 :
    recurrence5Scalar1First.coeff 326 =
      -(((((1578213939604285794504102552260410188104699242411122183 * 10 ^ 70 +
        6652125034650823676931817770304086397280619744937053428645940861609837) * 10 ^ 70 +
        4005540149356725803029621221223983942560225420175068899544049066821443) * 10 ^ 70 +
        7105433089884602799971233782949388905342895621475840285732497693310857) * 10 ^ 70 +
        8302492739614118112380594168668634887865926917082887924980110927695579) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 17 +
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
    rw [show 182 = 9 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (327 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_327 :
    recurrence5Scalar1First.coeff 327 =
      (((((717125476711076084734857112674628463885512541371503227 * 10 ^ 70 +
        7206944381105199846595897291232371591328691285947131084160952959250658) * 10 ^ 70 +
        4125575009322899145207561445685986533665150454562385448014997866660259) * 10 ^ 70 +
        0750296119322715290441188324412075278211010575918818988727371483802184) * 10 ^ 70 +
        1266435540829355320404961396489257571291661425971683651849054682405847) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 18 +
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
    rw [show 182 = 8 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (328 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_328 :
    recurrence5Scalar1First.coeff 328 =
      -(((((323113308283949676555563662549286869627861107543953761 * 10 ^ 70 +
        5646818251136644681777551535761008987959473571850858944301525062975401) * 10 ^ 70 +
        7136953072259222433715844305300089319304407301032734797740035676579139) * 10 ^ 70 +
        9300630095177794732199697475990359929477172136309279377706488475625525) * 10 ^ 70 +
        5537186694605721328269784523220994099360607537584129820382223339510118) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 19 +
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
    rw [show 182 = 7 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (329 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_329 :
    recurrence5Scalar1First.coeff 329 =
      (((((144293511584211002602904369551754503549650431288050989 * 10 ^ 70 +
        8486550632109172273410857247322023882643536910343689583933939044404846) * 10 ^ 70 +
        6099308526577690166625532966226114655631869100322282029180215773832233) * 10 ^ 70 +
        6294745882207706388368868402089580326422829367129557255625312417640404) * 10 ^ 70 +
        8382991705697558395548921429969684777397376759140302053065988028326836) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 330 = 20 +
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
    rw [show 182 = 6 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (330 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_330 :
    recurrence5Scalar1First.coeff 330 =
      -(((((63777525572508111949439343892223620488850571341149998 * 10 ^ 70 +
        2065889910508066718700866232383491285011378957054139974036246804504792) * 10 ^ 70 +
        0630562767860014142974022606304580411602983172540386341865905460041473) * 10 ^ 70 +
        6463014646190246225400686284958899827736407421075576265550365375216188) * 10 ^ 70 +
        2642445433702314761116871721823261358961330693597341690495873112426828) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 331 = 21 +
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
    rw [show 182 = 5 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (331 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_331 :
    recurrence5Scalar1First.coeff 331 =
      (((((27848296252667688220477042841878370954672188141891196 * 10 ^ 70 +
        6225021491657123245666047221944380894152102768426062694574769392052871) * 10 ^ 70 +
        1901512057119113449375473391103033308457235949786421895254630238394045) * 10 ^ 70 +
        1262282706426260739248373270040058291742353787020816477561781723814988) * 10 ^ 70 +
        7190029620522498671625542394625837017290203587911076052320360540745748) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 22 +
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
    rw [show 182 = 4 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (332 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_332 :
    recurrence5Scalar1First.coeff 332 =
      -(((((11988107447060372089640393952514123780298736210655561 * 10 ^ 70 +
        0963057708241608784952440232186691930181682203441791166967654664223820) * 10 ^ 70 +
        2429789283736722648915352939694304923028588958104721219387939173750181) * 10 ^ 70 +
        6184581697102794670328848560795339056764048856011848223940662561786270) * 10 ^ 70 +
        5717401892203729653545068760045295355852690534856815453608971228975285) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 23 +
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
    rw [show 182 = 3 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (333 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_333 :
    recurrence5Scalar1First.coeff 333 =
      (((((5077582201663134479213581660438201718161856486567266 * 10 ^ 70 +
        0749169382559354046313075830894215781841118938224181076809260797755971) * 10 ^ 70 +
        1683767874399672330153396253382198143488126173722825446319418362896626) * 10 ^ 70 +
        1772423836198601920087820828599856935544944881066586484321901029107992) * 10 ^ 70 +
        8326642255732399778771483545142290983206922694707223523811198498195491) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 24 +
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
    rw [show 182 = 2 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (334 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_334 :
    recurrence5Scalar1First.coeff 334 =
      -(((((2112124108941775558681141130576904879343115982018460 * 10 ^ 70 +
        7979855552486144468740402952937858754721964300790032237386238443040990) * 10 ^ 70 +
        3564032737077267462768303752880929267503293462444481188056530567209776) * 10 ^ 70 +
        4144343016235234946986427977308925789000380606894584733023087711143699) * 10 ^ 70 +
        4590171484291409600429338818935513548201719599756755055709446253647848) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 25 +
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
    rw [show 182 = 1 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (335 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_335 :
    recurrence5Scalar1First.coeff 335 =
      (((((861430896687833273624188078297222507696399542754242 * 10 ^ 70 +
        7229737859459512688069701864659871821702766672720911304481426753499721) * 10 ^ 70 +
        7814674474566207886234173407358711891445603792403170825665375320326608) * 10 ^ 70 +
        8887486805342392567423738995322471784751883227415735488889348896163839) * 10 ^ 70 +
        5886242660214992880597864477965320175125967760370790371757117607684394) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 26 +
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
  rw [recurrence5Scalar1First_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (336 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_336 :
    recurrence5Scalar1First.coeff 336 =
      -(((((343964606621482416564355080509787292516229906426425 * 10 ^ 70 +
        4900387294694258584415797779832985393051443852209066813402188311563928) * 10 ^ 70 +
        7590408414303290131755406751519101599823744434397473846401742692649329) * 10 ^ 70 +
        3443332874792173512371833096684043684494488498562337845233773192849496) * 10 ^ 70 +
        2366806546522154883545159940964872880462987599736330085913339365663534) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 27 +
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
    rw [show 214 = 31 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (337 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_337 :
    recurrence5Scalar1First.coeff 337 =
      (((((134277475880703789983423465647404235972430883772655 * 10 ^ 70 +
        3619506533416464134196776182670729330413737225674311520369358770303635) * 10 ^ 70 +
        5383545788782460291468431552834942668786905319505359581211775300335563) * 10 ^ 70 +
        5375314262739415743609079353444747053726519857279016752737270099694067) * 10 ^ 70 +
        0946890481648353028473794502116777522609906149918748586713095929874140) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 28 +
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
    rw [show 214 = 30 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (338 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_338 :
    recurrence5Scalar1First.coeff 338 =
      -(((((51181656995983686257187786656969994052373199027298 * 10 ^ 70 +
        0538997499777823055889579790153437265453107621786431709314895968983809) * 10 ^ 70 +
        4011896240281190120552320499807914957669571337067664772229769034711642) * 10 ^ 70 +
        0635474278329304939842040166858605813541933738966631311248035121057804) * 10 ^ 70 +
        9795406921399760874976890219047035987289759226911705461557998161113494) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 29 +
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
    rw [show 214 = 29 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (339 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_339 :
    recurrence5Scalar1First.coeff 339 =
      (((((19022225779819436911170683787226822088588210069184 * 10 ^ 70 +
        7496594586991660890802427418974132222943470467539189049655883109347218) * 10 ^ 70 +
        7480911993756048048832174461586812445365941467523720562635263659690427) * 10 ^ 70 +
        2216775405468166672729610306451211819570383201026709359102623019800011) * 10 ^ 70 +
        7258162304526445839248629983913238071442114323286790816741054815055192) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 30 +
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
    rw [show 214 = 28 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (340 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_340 :
    recurrence5Scalar1First.coeff 340 =
      -(((((6883452557500582723732564944676818989093951778181 * 10 ^ 70 +
        5657032636600749199852124307737144068477099504556454015633046844118692) * 10 ^ 70 +
        5117067225858132954637184696627010527535577153171027574237457712135877) * 10 ^ 70 +
        4416544275516020771304707240728394715298928790645002804101603712264506) * 10 ^ 70 +
        3251924683934275618841176223568487984282264019483097734022878799554208) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 31 +
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
    rw [show 214 = 27 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (341 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_341 :
    recurrence5Scalar1First.coeff 341 =
      (((((2421074148833925857422659988156205836192686640808 * 10 ^ 70 +
        1784603394575772895137737748555366373670489690503213247162560611658704) * 10 ^ 70 +
        2119282579684193720625426453795156147978470805439188053469501083992398) * 10 ^ 70 +
        3830594260965522618122040831535218751040521652560116904610143260749049) * 10 ^ 70 +
        3864674896681984893634730111372509120450759008579810057922455521220941) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 32 +
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
    rw [show 214 = 26 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (342 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_342 :
    recurrence5Scalar1First.coeff 342 =
      -(((((825944425565597992098930904607766428868299321545 * 10 ^ 70 +
        0733189528547354830139275407838176948954742840428128570183382041773588) * 10 ^ 70 +
        1028547987749073046498560053571672615441033336827442217637227552296258) * 10 ^ 70 +
        7284258766074945329423516711788897692965505556543487778814394573952387) * 10 ^ 70 +
        0689004604461730531646532275917446939917015452224428280464100655408905) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 33 +
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
    rw [show 214 = 25 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (343 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_343 :
    recurrence5Scalar1First.coeff 343 =
      (((((272545036432642248449913610808289642773797449502 * 10 ^ 70 +
        0865370856987828989846036895250000755163753049356770160039572838928567) * 10 ^ 70 +
        0337972831207735596340828402600158291492971634806442720564955364232804) * 10 ^ 70 +
        2579179867141142484152510162728946487813638713885651117863198851394833) * 10 ^ 70 +
        4736595085542054367186759989693590139972389955370914247338087892980378) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 34 +
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
    rw [show 214 = 24 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (344 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_344 :
    recurrence5Scalar1First.coeff 344 =
      -(((((86661184692212155204028502130230097566969289006 * 10 ^ 70 +
        1630249083388338078541856874236450002097159839599830615327175681543534) * 10 ^ 70 +
        1630669677272325687397132917367333932231114016794979197417135914601469) * 10 ^ 70 +
        6936591310056099576657167290696549971896891936028405106744373966345418) * 10 ^ 70 +
        5603951305854609422419378116400471828264242843109526173307504789603518) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 35 +
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
    rw [show 214 = 23 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (345 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_345 :
    recurrence5Scalar1First.coeff 345 =
      (((((26407261497637128038449579657451219442527432279 * 10 ^ 70 +
        6376591980543771000189772903412168595373916633655788316329530427158109) * 10 ^ 70 +
        4708849396461936422801134434457475958453650504391524416707974076659031) * 10 ^ 70 +
        9300582864211048943589540356679161211176936852911223536987128113024127) * 10 ^ 70 +
        4879512844947932907472196448820538586113623386240213899760171732066569) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 36 +
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
    rw [show 214 = 22 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (346 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_346 :
    recurrence5Scalar1First.coeff 346 =
      -(((((7646465484935683696688790537602349436843957859 * 10 ^ 70 +
        4151855299306168711621969688688416068361099585395414229629222318786260) * 10 ^ 70 +
        1069580630455494734094943319870441014648343043352639290530354005946523) * 10 ^ 70 +
        4490643886307613745357428485436996683243042791589491679979692195886283) * 10 ^ 70 +
        9546268126221290491986464289528294876572000752931447883825765051068379) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 37 +
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
    rw [show 214 = 21 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (347 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_347 :
    recurrence5Scalar1First.coeff 347 =
      (((((2074573246450945604634537189258961584375810611 * 10 ^ 70 +
        3969442061365417166272669036150348664645371574590602643930246041620930) * 10 ^ 70 +
        7519566362352653996939341856383540328965927825363059913470644561643418) * 10 ^ 70 +
        8626497658061507378747306287392911920911553887078906546697979411503820) * 10 ^ 70 +
        1900224423741073477245120285775562235120328840032596459880115611801897) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 38 +
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
    rw [show 214 = 20 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (348 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_348 :
    recurrence5Scalar1First.coeff 348 =
      -(((((513781204995698839180337955999243617658072854 * 10 ^ 70 +
        7819538941790539349725114682004592170472442150319357626595895210299743) * 10 ^ 70 +
        1976981064034179192711864729886125332210634134049968737598143889179762) * 10 ^ 70 +
        4777872001586915317594232978723929390218282655146291870125995816375993) * 10 ^ 70 +
        6846746215443180906489602221944651731946605699693569699506934610012406) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 39 +
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
    rw [show 214 = 19 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (349 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_349 :
    recurrence5Scalar1First.coeff 349 =
      (((((109573748602307036786157238495702273765348857 * 10 ^ 70 +
        5819918268507981600196591229154183913778500294905252019514451545886045) * 10 ^ 70 +
        6696512783056589515550347398210952671933173724134324540800218944980657) * 10 ^ 70 +
        2338891285289348329984039855094920571975322020010943392268900003816029) * 10 ^ 70 +
        7522117372922774921720353771749177303712763290512950255572618584575815) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 40 +
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
    rw [show 214 = 18 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (350 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_350 :
    recurrence5Scalar1First.coeff 350 =
      -(((((16683141029293490434671094650622488690697787 * 10 ^ 70 +
        9075554521073425155205705472534334997314225229604209581185199984309244) * 10 ^ 70 +
        9256572346604440020415154222615816438494564691711364844757999957837190) * 10 ^ 70 +
        8932010492685079934085859652140769719705256198492441338495307611666383) * 10 ^ 70 +
        4163810391018881534533869455494732726218017035616413199012610930245320) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 41 +
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
    rw [show 214 = 17 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (351 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_351 :
    recurrence5Scalar1First.coeff 351 =
      -(((((285381158898765464524698682941970779550486 * 10 ^ 70 +
        3411723459850214469503767372984611159640983668217018087473681973098606) * 10 ^ 70 +
        4465700453827370221787580129073673446382096299203348689721751470406729) * 10 ^ 70 +
        0433892024021289532968660396312605671433708171951154302961319160993835) * 10 ^ 70 +
        7676541204125842616263983900582457661194109557648783529986182472896059) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 42 +
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
    rw [show 214 = 16 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (352 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_352 :
    recurrence5Scalar1First.coeff 352 =
      (((((1620239258703696961420636505292678956453321 * 10 ^ 70 +
        0224410512095851648480244195841041442633648405622820912325465342548203) * 10 ^ 70 +
        3607112184147362594914670818008480911149543814544348014449107740632189) * 10 ^ 70 +
        4523431040185284135763129203297734193982880899982284141237733919051712) * 10 ^ 70 +
        2511274082692528122272630987793262149351000172314095493173375353048606) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 43 +
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
    rw [show 214 = 15 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (353 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_353 :
    recurrence5Scalar1First.coeff 353 =
      -(((((857975872361741276875270217544917342716543 * 10 ^ 70 +
        2953978748912738946662900542447952548416887732825890018677693581557050) * 10 ^ 70 +
        4873580916062880528051548353128309395109374804353357427038403373633731) * 10 ^ 70 +
        4352608043446063292797513432500620233933436485080550883862364896924948) * 10 ^ 70 +
        2200561231682852547946082427916967387949651275102065469616574187290803) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 44 +
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
    rw [show 214 = 14 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (354 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_354 :
    recurrence5Scalar1First.coeff 354 =
      (((((315493911418897158506124639598713173903034 * 10 ^ 70 +
        3578108274753542656979865107107565392487157752355215477459694609480164) * 10 ^ 70 +
        4398381884409965878142976491646415536129011644051447011771643900291392) * 10 ^ 70 +
        5969331921102474853663099531809527996090303924048922473501985746548688) * 10 ^ 70 +
        1258123823299467369644085421839015411103134500377630507869378385009956) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 45 +
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
    rw [show 214 = 13 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (355 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_355 :
    recurrence5Scalar1First.coeff 355 =
      -(((((86656042232116785260112546393807792931762 * 10 ^ 70 +
        4206569531596472897099322676181994704968060155656614635098902042917944) * 10 ^ 70 +
        7396573488281556877473248977324911783299132603295685570617208940933826) * 10 ^ 70 +
        5417816251927091824064588683437580966322166181083712266105843075365335) * 10 ^ 70 +
        9829622488406404915661425582652779479958710001746654654597182313724196) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 46 +
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
    rw [show 214 = 12 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (356 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_356 :
    recurrence5Scalar1First.coeff 356 =
      (((((12883342075622462695642017686300498738565 * 10 ^ 70 +
        7197094972842541988063449472112131878272301013744857565265548507881025) * 10 ^ 70 +
        0864359264930537452961937578202455400662396589662720106828287815460032) * 10 ^ 70 +
        3730353906321693718488362486037561019522178899689712459396649581868905) * 10 ^ 70 +
        2973770546818503553698797446220017260589872303173796503013319830231927) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 357 = 47 +
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
    rw [show 214 = 11 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (357 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_357 :
    recurrence5Scalar1First.coeff 357 =
      (((((4241933652794903980038979094450014220593 * 10 ^ 70 +
        2163435224571229535225300773454498710377064018408499717207783219422801) * 10 ^ 70 +
        6771364965577479813656497936356397100893424249264190293254719052014155) * 10 ^ 70 +
        1272597674836380473948313961960987191097556269930081090164452490888965) * 10 ^ 70 +
        0344503799991520410943711203355672348927669467870686820680853369184921) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 358 = 48 +
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
    rw [show 214 = 10 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (358 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_358 :
    recurrence5Scalar1First.coeff 358 =
      -(((((5233193743665091234455612255090370122128 * 10 ^ 70 +
        1367004040781512731249095944295443716126636292170939310063471214037893) * 10 ^ 70 +
        7862677396366377086534295556823828465183670241371775928439247703695922) * 10 ^ 70 +
        6484617160926687402606541131040325785728175929400970877302353922054689) * 10 ^ 70 +
        0766754216088821049102158274485064408614315684768408329111108647818009) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 359 = 49 +
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
    rw [show 214 = 9 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (359 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_359 :
    recurrence5Scalar1First.coeff 359 =
      (((((3289068962024230959098481955407776983791 * 10 ^ 70 +
        5336335151875595418485129371362758594999264560904118412968622955877713) * 10 ^ 70 +
        1966620693372017335131728563354766036206037121814988051028142018296004) * 10 ^ 70 +
        0490043472110442200472945773671060391753285139444106806326239929577943) * 10 ^ 70 +
        3725342654500459653473593773380910573157020242392783696540051055133448) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 360 = 50 +
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
    rw [show 214 = 8 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (360 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_360 :
    recurrence5Scalar1First.coeff 360 =
      -(((((1677740149393132308235644522137431778020 * 10 ^ 70 +
        1522513394891437571504097878192279330982576659837493088732436921148057) * 10 ^ 70 +
        8302556817145714355499176844044493797528715180072091934620837955372960) * 10 ^ 70 +
        1558443463001061975143244595920241695231403728842994540890724447987352) * 10 ^ 70 +
        8235847140111399309065052068213838278925394403408499905591415657198312) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 361 = 51 +
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
    rw [show 214 = 7 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (361 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_361 :
    recurrence5Scalar1First.coeff 361 =
      (((((765519012014617913715736388503784061595 * 10 ^ 70 +
        2652507109252749923876217423705936300885773322830520135059971031838378) * 10 ^ 70 +
        3987329848995108332372083760030307414471558795942816824133253015496247) * 10 ^ 70 +
        0523736812789229799828268069664022659423488713539531749238661365219228) * 10 ^ 70 +
        9440445675039723015355747400611748810210290050779692527630058825882624) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 362 = 52 +
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
    rw [show 214 = 6 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient0.coeff x * recurrence5B2A3.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B2A3_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1First_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (362 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_362 :
    recurrence5Scalar1First.coeff 362 =
      -(((((324501231123546288074324545749941353150 * 10 ^ 70 +
        0538129153129808754553729545060449409816558984153392179871031459844753) * 10 ^ 70 +
        1280273957656097472500102874426026259777953802755113796893790676470569) * 10 ^ 70 +
        6667471773004062330649175952561075312606739326723731608148184054783607) * 10 ^ 70 +
        0974547247856922553475139552355469320269435791617390482411491069594476) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 363 = 53 +
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
    rw [show 214 = 5 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1First_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
