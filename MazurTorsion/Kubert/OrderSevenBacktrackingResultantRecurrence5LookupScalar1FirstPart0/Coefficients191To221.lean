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

private theorem recurrence5Scalar1First_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (191 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_191 :
    recurrence5Scalar1First.coeff 191 =
      ((((((738816312 * 10 ^ 70 +
        1113593829260188473041699494848987669556371348024038821648446501449851) * 10 ^ 70 +
        1957525928949198051183941270335472065103528290229217408598568557146955) * 10 ^ 70 +
        1467970333792300720518159061543831147998110846403034103738661586632622) * 10 ^ 70 +
        3494437431597950429923811899351891934059103274826716466595396993432929) * 10 ^ 70 +
        7771530725685850024689794048628834469531447809532206369312360287340552) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 0 +
    192 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 26 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (192 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_192 :
    recurrence5Scalar1First.coeff 192 =
      -((((((987254234 * 10 ^ 70 +
        8169284415772988928698696872796492735831151498887044137935155161028020) * 10 ^ 70 +
        3744407452596307353247354876458451554042404980947417224974886174395205) * 10 ^ 70 +
        0688371657859488232646872397432507043340366220531221332600224106801123) * 10 ^ 70 +
        5024365962848050423340089318148996495701043995382732638807304580234429) * 10 ^ 70 +
        9471566215126976571550495375029384781993776917567569333566827015293652) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 0 +
    193 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 26 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (193 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_193 :
    recurrence5Scalar1First.coeff 193 =
      ((((((1295761083 * 10 ^ 70 +
        3851208858931904205543838793254927303271184508087703765746900566034495) * 10 ^ 70 +
        8897059030666177663877785615222102492055462289938926097543468525204324) * 10 ^ 70 +
        6677215854681933456430615114195438115563944502405364205235280932643587) * 10 ^ 70 +
        1132168497073770699579513921157716668897868592231845079576622669779566) * 10 ^ 70 +
        4256250412544910021662797975319170223591530629576444713347939597909854) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 0 +
    194 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 26 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (194 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_194 :
    recurrence5Scalar1First.coeff 194 =
      -((((((1670268350 * 10 ^ 70 +
        9457385006229256882400361342158932051907256385367529007732605777801621) * 10 ^ 70 +
        9324064525037639174549691092154604116881961814006141516430133366106720) * 10 ^ 70 +
        9128608686390570124319880642402557030311118243345069912476644238319457) * 10 ^ 70 +
        6068386907285914072521128460083446380546788036460530468217151254721722) * 10 ^ 70 +
        1375362735602915315098370973878125550227367805849796081063230953374488) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 0 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 26 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (195 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_195 :
    recurrence5Scalar1First.coeff 195 =
      ((((((2114308552 * 10 ^ 70 +
        6465418401520903317444677386378639278626675188049537616277181225250101) * 10 ^ 70 +
        1846974091374205591605686564447082654692709570986702609591124696765392) * 10 ^ 70 +
        7319784660726744195574188812372722642731875625462360262382413291163679) * 10 ^ 70 +
        5919000793849875159055371388348034467251786669643325362674996956526173) * 10 ^ 70 +
        6265695133834382262117793093979470719734433614202090268259796532560520) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 0 +
    196 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 26 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (196 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_196 :
    recurrence5Scalar1First.coeff 196 =
      -((((((2627961735 * 10 ^ 70 +
        3399372156077828654803298915859156766296786675947594397514351610773930) * 10 ^ 70 +
        8011095984407595599501988700746068309574879691224336323027699938926482) * 10 ^ 70 +
        4182774510480166431414517214932145842416501804567059406518667383744434) * 10 ^ 70 +
        0900576893066910343399228550227063929017277621567418186380458157247312) * 10 ^ 70 +
        8903005273972384417306892709799161356559661276130853420738835950636535) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 0 +
    197 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (197 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_197 :
    recurrence5Scalar1First.coeff 197 =
      ((((((3206838578 * 10 ^ 70 +
        0173364728232425111673462697886272003598135096562465431218037325159270) * 10 ^ 70 +
        1534574551747601512649713287452645846150434109497158180809771106982861) * 10 ^ 70 +
        0261119948236186346348518656831313182121532698177400900428329649653627) * 10 ^ 70 +
        1070990821501638260450395651659337794626831808837989660150418855732890) * 10 ^ 70 +
        5666824145284953697058242649986018677638119028935232007328488727103016) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 0 +
    198 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 26 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_197_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (198 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_198 :
    recurrence5Scalar1First.coeff 198 =
      -((((((3841234956 * 10 ^ 70 +
        2203480349625745018590134461235091250277750366512686405702796671996625) * 10 ^ 70 +
        2442355470916074035605248451626867620272073396886173099633092144158600) * 10 ^ 70 +
        0658533300890481552618192616151569499531886172257920046076209495708979) * 10 ^ 70 +
        9065959131594953137530320172281704874340489073696201604150172638370242) * 10 ^ 70 +
        6256951318572850551031925700103268412060527572169087846097590337223691) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 0 +
    199 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 26 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_198_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (199 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_199 :
    recurrence5Scalar1First.coeff 199 =
      ((((((4515607386 * 10 ^ 70 +
        8252349865594140020551552303661862185232848491216361781062920677813992) * 10 ^ 70 +
        1888676742328486121270219954105039284547515475965928576037058594645225) * 10 ^ 70 +
        0520924965251348273282963610747051843776383391046860271066420091545720) * 10 ^ 70 +
        6702390261930564379117199284509497954913956888771911956049671545324247) * 10 ^ 70 +
        9271169593082534475634438809707523038096483178368803129023340366474303) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 0 +
    200 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 26 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_199_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (200 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_200 :
    recurrence5Scalar1First.coeff 200 =
      -((((((5208513817 * 10 ^ 70 +
        1751559145729882177724467285039951123970756505922277474693237826919993) * 10 ^ 70 +
        0220977678922377611482235811818166048743820282362747994107557254518941) * 10 ^ 70 +
        0416340165811939882467092807260260873352891092549923219795084585360441) * 10 ^ 70 +
        4612167038508846245041890453499612108454655935957498154151769559532891) * 10 ^ 70 +
        9653487709109433931447765220211984984312706297583844618807063056607044) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 0 +
    201 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 26 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_200_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (201 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_201 :
    recurrence5Scalar1First.coeff 201 =
      ((((((5893135461 * 10 ^ 70 +
        1796262521442511608105289687386476181397049099388782534452251348668678) * 10 ^ 70 +
        0102403197995172437057542662755628522430687062791369258043305216577398) * 10 ^ 70 +
        8075757282638080994627844826402665547270402972163362912596933624651229) * 10 ^ 70 +
        7348093052527698944571046109843576333418780354331001770648850490479125) * 10 ^ 70 +
        7049043268061827010469477883733414209752942240779886184112459857330522) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 0 +
    202 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 26 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_201_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (202 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_202 :
    recurrence5Scalar1First.coeff 202 =
      -((((((6538441950 * 10 ^ 70 +
        0291300320198007005883918835234561488042068155985157545687228317826643) * 10 ^ 70 +
        3414254963620943160723156071534150313754879575493796965368921967803668) * 10 ^ 70 +
        2092634183267878644190057540255740934853515965080370799204900061860790) * 10 ^ 70 +
        9031381993846141793041597575067254143877442859911186521331225796313534) * 10 ^ 70 +
        9214805906340154270851518436420107387954599306815347531439443952377380) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 0 +
    203 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 26 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_202_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (203 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_203 :
    recurrence5Scalar1First.coeff 203 =
      ((((((7110987566 * 10 ^ 70 +
        1913624227049615073528724273193381455197229497354697024989524280867458) * 10 ^ 70 +
        7031804654797367663982917084334948055184538942319312257201027654814410) * 10 ^ 70 +
        5589102250907948098692814650878376031223729140285406890172955133942662) * 10 ^ 70 +
        2863923107946767903632153949320725319919806805901844405408362714976177) * 10 ^ 70 +
        0438338337010420395023120169693534279124118428833235947185315834299622) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 0 +
    204 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 26 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_203_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (204 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_204 :
    recurrence5Scalar1First.coeff 204 =
      -((((((7577239116 * 10 ^ 70 +
        5197291147157876451044808732803473865139284470634056935880581906312103) * 10 ^ 70 +
        7903697595587733849854791763180781490755489546344579202135338312054276) * 10 ^ 70 +
        9034646324068152156179376069807647519449298013378900894109930658533776) * 10 ^ 70 +
        0639003706077947210783609774451943958697189005881802539605337389949050) * 10 ^ 70 +
        4466072084965543012841388484051096061229972463372343685662634640638109) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 0 +
    205 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 26 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_204_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (205 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_205 :
    recurrence5Scalar1First.coeff 205 =
      ((((((7906248436 * 10 ^ 70 +
        3217119855203330097876793503296416794573664478627339519914774574814010) * 10 ^ 70 +
        7870236262339957659508747795158532584699200851737935858030576009447859) * 10 ^ 70 +
        5562006413642773362687917882980047725679083910171707486033333118802551) * 10 ^ 70 +
        4460065794517861128078674377161530244445434415061376051751939953491873) * 10 ^ 70 +
        0884089015494777655280191134838921156558950479350230035326082087962345) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 0 +
    206 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 26 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (206 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_206 :
    recurrence5Scalar1First.coeff 206 =
      -((((((8072409222 * 10 ^ 70 +
        1901086579729513573688328304781893434893658652530698444349273171974533) * 10 ^ 70 +
        8034412934349725305130795685206430740498048341162623472623355578056485) * 10 ^ 70 +
        2862652164795050371183489395306320577650978589961872614917593602350573) * 10 ^ 70 +
        7938312104381686048715904227581347114024495773532362693763115934951976) * 10 ^ 70 +
        1755221568180402057781972410276461932665946077977645373379363538793512) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 0 +
    207 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 26 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (207 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_207 :
    recurrence5Scalar1First.coeff 207 =
      ((((((8057993187 * 10 ^ 70 +
        8242523605345971190032706087716770663451211658118556090071300773064576) * 10 ^ 70 +
        9975916804795895813904258435460080234211803758688718407682372927295944) * 10 ^ 70 +
        2964627704808166327689738743662434132033996272594497828183886334263769) * 10 ^ 70 +
        6286491510153814743263498920427617429212405126591925610893251363553555) * 10 ^ 70 +
        2877642560211683667032798820626265242260706011448024198777627594655746) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 0 +
    208 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 26 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (208 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_208 :
    recurrence5Scalar1First.coeff 208 =
      -((((((7855155542 * 10 ^ 70 +
        9417214341889542476450589910659372086672566661817432728301650344442283) * 10 ^ 70 +
        0360063916423757968986381089092534571477246266866995096834639143656028) * 10 ^ 70 +
        2086680380299382952581578131960772657891859633024570000395869974579196) * 10 ^ 70 +
        5706292230834124105446109537700990635031578728761596352734443614219273) * 10 ^ 70 +
        4588384163145128536615767015905008967851846706858044818971892402958243) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 0 +
    209 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 26 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (209 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_209 :
    recurrence5Scalar1First.coeff 209 =
      ((((((7467139806 * 10 ^ 70 +
        5780174956118981641370887698419039802725262433215760611881234787807159) * 10 ^ 70 +
        1663021281895325637192897311990977078928736239283868669221385567337237) * 10 ^ 70 +
        5003917108272337020491199755393797440914462012126769330207970938431003) * 10 ^ 70 +
        7695234095270866223886349592820433174919640658060074728155279122900685) * 10 ^ 70 +
        3391485222482785750361750458008893276760330118164230751199750389398639) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 0 +
    210 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 26 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (210 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_210 :
    recurrence5Scalar1First.coeff 210 =
      -((((((6908494753 * 10 ^ 70 +
        3509291741487860635553214088098688658892389657499597102666286194580413) * 10 ^ 70 +
        7424177155166796973971228322679020672011179790418317389638819116000352) * 10 ^ 70 +
        7760907371624213978032895441020526643216220121444981471745048938967095) * 10 ^ 70 +
        9068871479417476031917661337061498057095018135737692482844129496542041) * 10 ^ 70 +
        3123477463204868996100530288818742068816728741047940018251974354145855) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 0 +
    211 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 26 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (211 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_211 :
    recurrence5Scalar1First.coeff 211 =
      ((((((6204231811 * 10 ^ 70 +
        4000827400872709616964494355538786288584421011567051928739794029979597) * 10 ^ 70 +
        4137454689236479778530806429163324738679536918084032574900061757971357) * 10 ^ 70 +
        1590455374134709825952925803980150332481906637589273495816126490882943) * 10 ^ 70 +
        4052263070888613416425548483468186945848115856571946513130975045676888) * 10 ^ 70 +
        7082070289033444372202088633652398507429088239165500930955133038328110) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 0 +
    212 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 26 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (212 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_212 :
    recurrence5Scalar1First.coeff 212 =
      -((((((5387982952 * 10 ^ 70 +
        8486959036498659787530795245324502496158792883386790178685083050579638) * 10 ^ 70 +
        2821268703646673904621024340313799405696360506621686765077862534979867) * 10 ^ 70 +
        5039332313410794501934894814892819861056275791704755334563652687307897) * 10 ^ 70 +
        4013886238864461925550754568588473098005291394966401820504634366392564) * 10 ^ 70 +
        5949015246896409242734889651697664523505247405803532772559623919114586) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 0 +
    213 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 26 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (213 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_213 :
    recurrence5Scalar1First.coeff 213 =
      ((((((4499346795 * 10 ^ 70 +
        1222226726058061380588864178632347144006563012588399185061188055190452) * 10 ^ 70 +
        8737211799019432741744303172923613385073775671319922155512887744315054) * 10 ^ 70 +
        2682378141099257888656350623855294981055276581669827605850430284773560) * 10 ^ 70 +
        4925999937394022949053468996607696058701348152080899333999834011687820) * 10 ^ 70 +
        9787329637272277389605840900228958869853945542194412191641072885923046) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 0 +
    214 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 26 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (214 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_214 :
    recurrence5Scalar1First.coeff 214 =
      -((((((3580713991 * 10 ^ 70 +
        1944763633669761528043395299286397455191362504853059581008087142613053) * 10 ^ 70 +
        2639238270442539916550283066274359680456555538237418873027267438462599) * 10 ^ 70 +
        2847568852832134403877431494042818731752485302980423704365193967458222) * 10 ^ 70 +
        3015369905555403210690423246369987663614454261753294535246393925420565) * 10 ^ 70 +
        9619506661034416038265349462400387001899250761652030522050170115061968) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 0 +
    215 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 26 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (215 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_215 :
    recurrence5Scalar1First.coeff 215 =
      ((((((2673925561 * 10 ^ 70 +
        4196216206697819582203051929014366977372042464376502868797048790996736) * 10 ^ 70 +
        3894676170742633998428964954626634912758348642206212091461260989079376) * 10 ^ 70 +
        1665530188907545866312695314480126281588943612710523902626196402471760) * 10 ^ 70 +
        8105756472662890290112101554048268072275337535187427833602530602236582) * 10 ^ 70 +
        0903163721131406717057437842857384149198982713680457226479342355292035) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 0 +
    216 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 26 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (216 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_216 :
    recurrence5Scalar1First.coeff 216 =
      -((((((1817130084 * 10 ^ 70 +
        4765070570878638598107520127187721560837110510780371529677552573778618) * 10 ^ 70 +
        2442657081105526210848443873092492438543175431017732871345640002647431) * 10 ^ 70 +
        0391862905406200102552765540340369551948824379140593401842289584552545) * 10 ^ 70 +
        5722024354759555928761084665789093214684522787959771038528626035200966) * 10 ^ 70 +
        3141999191655551516866089880791053844731684478561428003347941249507323) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 0 +
    217 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 26 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (217 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_217 :
    recurrence5Scalar1First.coeff 217 =
      ((((((1042166786 * 10 ^ 70 +
        9714083735609125131544764258812929077895572138211268023450892353316538) * 10 ^ 70 +
        8211509472567083148755340809488054459281312062261043630644070638685783) * 10 ^ 70 +
        0958085894376163943381046724677963204767523896368314144451887591717765) * 10 ^ 70 +
        4289128348650206389545389696164242303736106990664309131036442446136260) * 10 ^ 70 +
        9505810660407140281719854989062649377312905864225857617684431205495326) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 0 +
    218 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 26 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (218 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_218 :
    recurrence5Scalar1First.coeff 218 =
      -((((((372719393 * 10 ^ 70 +
        8649882912349107463480323940820090973461973212654863585472471013731768) * 10 ^ 70 +
        0113570519725671526635669177614581229772269817889399874840622195927197) * 10 ^ 70 +
        5029191081232869750175086653897571913755321148481776323831471987048878) * 10 ^ 70 +
        7462118253019616885280207817702073617781976324892455422425401374905699) * 10 ^ 70 +
        9423147806887945856294586878114850868565642912872785438751153051863912) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 0 +
    219 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 26 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (219 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_219 :
    recurrence5Scalar1First.coeff 219 =
      -((((((176625097 * 10 ^ 70 +
        9055082972459972200630153281327092263725593222715907645462060111025473) * 10 ^ 70 +
        4807419048530039291170013787999435041802469969485180280853453412179871) * 10 ^ 70 +
        4353118367208060353939242291028280711143413591561627179121853917851616) * 10 ^ 70 +
        9634800287325989972416898116712409733320943186967277152590159314564836) * 10 ^ 70 +
        0180413710071007098052315724365965731035879891840126808187713092022207) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 0 +
    220 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 26 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (220 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_220 :
    recurrence5Scalar1First.coeff 220 =
      ((((((600399113 * 10 ^ 70 +
        2295345586407675815478678279651300327255992209819305969268665924992468) * 10 ^ 70 +
        0274864063747804394937772294934242807923378240104999100251293985627565) * 10 ^ 70 +
        6857543407890485184063102422753119931917612449710281327295646664272981) * 10 ^ 70 +
        8006581985964861235746590249061721999522434429996281209049839240955731) * 10 ^ 70 +
        3619503606161209397861077440902912861100696262649601846517375538389374) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 0 +
    221 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 26 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (221 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_221 :
    recurrence5Scalar1First.coeff 221 =
      -((((((901456527 * 10 ^ 70 +
        6143077338653172402302141111940489493320412335702340763021874806654128) * 10 ^ 70 +
        4791580214442559705185053828645213382350372827247688731880136153738236) * 10 ^ 70 +
        4051056298239769723420718570583090155576843499360863134555768235771318) * 10 ^ 70 +
        6371788766000356327842768907050932178482277793214088293415290110106801) * 10 ^ 70 +
        7737916257909830441965002876259760593924204456477441294449232848243020) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 94 = 26 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
