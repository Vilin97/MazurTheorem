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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
