/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1FirstPart1Simp
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
