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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
