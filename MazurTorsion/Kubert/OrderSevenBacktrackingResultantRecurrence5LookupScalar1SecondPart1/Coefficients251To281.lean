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

private theorem recurrence5Scalar1Second_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (251 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_251 :
    recurrence5Scalar1Second.coeff 251 =
      -((((((168167 * 10 ^ 70 +
        7753203704125704647118816429363676039343149576077697213883344915481936) * 10 ^ 70 +
        1539852545518842695121543799831495608481631836340521302710684675166012) * 10 ^ 70 +
        5970021018431746402825555864836934319848281961298219435829822075709147) * 10 ^ 70 +
        2152051694784507552233366519696191095057059356663926746127406816146735) * 10 ^ 70 +
        5016082391107088139086554684116889209798785834776344352605511329479718) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 124 = 22 +
      102 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (252 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_252 :
    recurrence5Scalar1Second.coeff 252 =
      ((((((127448 * 10 ^ 70 +
        2101747699837810150649622792086179620078961799596432081757626696936846) * 10 ^ 70 +
        1242444132460229573843149289270242324928213822284495042700853202532182) * 10 ^ 70 +
        7235581065645885158233948118799631792050822913175907037826565365902931) * 10 ^ 70 +
        7174947543766738541133610283616627183836662830020140589433782944602846) * 10 ^ 70 +
        1050314583192539006149341747504071018912926416487675688924466092581428) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 125 = 22 +
      103 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (253 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_253 :
    recurrence5Scalar1Second.coeff 253 =
      -((((((93249 * 10 ^ 70 +
        2465333837700435325173111011249234014895504610619275654448149244690769) * 10 ^ 70 +
        1158957848424374804425013577812849671962060958058213631454648036936521) * 10 ^ 70 +
        2709628398746617186967696750105222357029742049048870224196717533974750) * 10 ^ 70 +
        7349688501289124335934673569582702027486014496844250179814489011579986) * 10 ^ 70 +
        3353869287162440612380112454352412252872978471703238808425144070463636) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 126 = 22 +
      104 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (254 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_254 :
    recurrence5Scalar1Second.coeff 254 =
      ((((((65941 * 10 ^ 70 +
        0452879929095953068662320403245152666176076766504300927970664380993351) * 10 ^ 70 +
        5205143399020700551128405788032037558501903675564011752713573498260250) * 10 ^ 70 +
        1448288142256186961458062762716014721920546891268891422716775503663808) * 10 ^ 70 +
        2147683830874603794465613034138090521384052076336630984524524403336320) * 10 ^ 70 +
        8090084546230445555448713059390045707964768056751862007431437354175042) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 127 = 22 +
      105 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (255 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_255 :
    recurrence5Scalar1Second.coeff 255 =
      -((((((45070 * 10 ^ 70 +
        7520423631996774869891960218071209872079149074802820285115773980936703) * 10 ^ 70 +
        1856744910318515633213701088937895292024335045226416922917393406134412) * 10 ^ 70 +
        9742739984826683330421537826355371684262694477122056828962274058235148) * 10 ^ 70 +
        3295576739712489851904606150651835594091224742576186597782485740650616) * 10 ^ 70 +
        4023336374027437960223808022251565841582924593825672950116251707074055) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 128 = 22 +
      106 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (256 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_256 :
    recurrence5Scalar1Second.coeff 256 =
      ((((((29750 * 10 ^ 70 +
        8295210814976233042524248003873871503581989618475277572579034256133536) * 10 ^ 70 +
        6510526570048151562458704864388095453285763502615654874852606624971004) * 10 ^ 70 +
        6688352146737806759276725117571201736163883783279813834421032816801759) * 10 ^ 70 +
        3583096602217804192831368944802474667421797099325756881072527201483557) * 10 ^ 70 +
        6592096445776464836168964216198183920034536593963551283480815148858632) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 129 = 22 +
      107 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (257 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_257 :
    recurrence5Scalar1Second.coeff 257 =
      -((((((18931 * 10 ^ 70 +
        6262197952279786431803775746597995870190025556471840620085949559893758) * 10 ^ 70 +
        0071622366514698085684123159649895219246117424483140294766565528234810) * 10 ^ 70 +
        5468806257419560149501682516223500929833571198055973123892563854020392) * 10 ^ 70 +
        8060846869836199699239162751892934854718291841948279768788990004483423) * 10 ^ 70 +
        1160398281672330596990570263358026079814977588890792743660358876243283) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 130 = 22 +
      108 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (258 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_258 :
    recurrence5Scalar1Second.coeff 258 =
      ((((((11578 * 10 ^ 70 +
        6184407113968021230483955051896591551976510584998344681440814166202220) * 10 ^ 70 +
        1190203804647758272196864148306206131752967189393097435945598846932062) * 10 ^ 70 +
        2232455867994724175252080305785039802799418177720807241870452001503618) * 10 ^ 70 +
        5499531241859919303726506187390674416699786497443863003948529137250048) * 10 ^ 70 +
        1346139513463420270704355145753169587799639992861932214066294265016133) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 131 = 22 +
      109 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (259 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_259 :
    recurrence5Scalar1Second.coeff 259 =
      -((((((6774 * 10 ^ 70 +
        1075203246988008933018821556212117031727518708859640018819594585325671) * 10 ^ 70 +
        4083051147941404006260003448651440652135119629001831220628554742164941) * 10 ^ 70 +
        2717368762533887657060934865802602144423414046188492877644792570779805) * 10 ^ 70 +
        0337459544703453172794505786187026803280152462964440862752948428025983) * 10 ^ 70 +
        8202664678027568567086252557694450398527046487301509911990758095126381) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 132 = 22 +
      110 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (260 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_260 :
    recurrence5Scalar1Second.coeff 260 =
      ((((((3762 * 10 ^ 70 +
        9176921142197125234591334994409221071956472907904693379831291814355684) * 10 ^ 70 +
        1958786902637795513752094572114468993006759052160792484707435432202907) * 10 ^ 70 +
        3032557905132732788524752779764659863785742460763951720582271293089308) * 10 ^ 70 +
        4830595984374647792517643381883859460829020973332582714106676661907701) * 10 ^ 70 +
        6374105134266098905808291073489710212214386256084296560613153853357821) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 133 = 22 +
      111 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (261 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_261 :
    recurrence5Scalar1Second.coeff 261 =
      -((((((1960 * 10 ^ 70 +
        1491511209769705145153768185195399697976288211427339913076363409033080) * 10 ^ 70 +
        4983774894020754519763129096639236420353115947977839542479110381144836) * 10 ^ 70 +
        6115880840821310314446896590589536403740357329095066570573003717256217) * 10 ^ 70 +
        8395393471562033617374067979609035552317739333062782228314099753012849) * 10 ^ 70 +
        1893342813388460190351971384702956332357578070343140696515128485363772) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 134 = 22 +
      112 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (262 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_262 :
    recurrence5Scalar1Second.coeff 262 =
      ((((((936 * 10 ^ 70 +
        2228911095030412635117882855422197942287044691218017785787681825319505) * 10 ^ 70 +
        3794960543416801035779929983336431563936692897394723033041703231909410) * 10 ^ 70 +
        6490359319923487419891231002176423527576295411664633934964225218762891) * 10 ^ 70 +
        0572268129783509027787556422653816559312934289500421498400095136338217) * 10 ^ 70 +
        2868451202306656643069793856563816497818285203894003690631555759524987) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 135 = 22 +
      113 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (263 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_263 :
    recurrence5Scalar1Second.coeff 263 =
      -((((((390 * 10 ^ 70 +
        8963835487216530439063707731100887392469889047636867279150916991625277) * 10 ^ 70 +
        2541113497477502511954700763419959269866818306070421196799215528678467) * 10 ^ 70 +
        6054072187770801937059488435442872292025180007248992591032895272546952) * 10 ^ 70 +
        9689175773154088436493159360370226135404709644396526676412411690026674) * 10 ^ 70 +
        7691811763007997709978795915163235431141119293305435803112766364886374) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 136 = 22 +
      114 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (264 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_264 :
    recurrence5Scalar1Second.coeff 264 =
      ((((((124 * 10 ^ 70 +
        3137834179435465635819306168815703549222403193032184471810124198948797) * 10 ^ 70 +
        8697225250570747143771788523718508980018227462387055436956362772154511) * 10 ^ 70 +
        1235158792870515931140580637893206729227273366786770177387819879420264) * 10 ^ 70 +
        3843449777792899126899314108481766769620700918298799084602210463791176) * 10 ^ 70 +
        6815814083324220360678548849968672726943327605086347509338433330738060) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 137 = 22 +
      115 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (265 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_265 :
    recurrence5Scalar1Second.coeff 265 =
      -((((((9 * 10 ^ 70 +
        9882128069152051868500558173103428544970096424551992635502655475716396) * 10 ^ 70 +
        6615435581188092806954415113210458625483882086773824646882333038669594) * 10 ^ 70 +
        5891054922689108969073353495893159042901683086189379950177536665567009) * 10 ^ 70 +
        3740770901196125165279204735434218324799305511867394842614585990437958) * 10 ^ 70 +
        5316316218570270050963380736137598067702093230372793805188924818411368) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 138 = 22 +
      116 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (266 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_266 :
    recurrence5Scalar1Second.coeff 266 =
      -((((((27 * 10 ^ 70 +
        8420853517245567823096933331791337059136386769106828489447100286280010) * 10 ^ 70 +
        0707901090337071372102368628763072579117478869232886511954442039229500) * 10 ^ 70 +
        8900529516151168571963491935863200132177288934355255253493774357965622) * 10 ^ 70 +
        6549181677238995632479234668442409704602633663216958136775362786362773) * 10 ^ 70 +
        2404841496485842367028793137124661892545481824187261614160141950495532) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 139 = 22 +
      117 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (267 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_267 :
    recurrence5Scalar1Second.coeff 267 =
      ((((((31 * 10 ^ 70 +
        7379548441622396406417329900484254571998190859602678154797477108636995) * 10 ^ 70 +
        3634406642334705054475001746301104818515813762024764356309440339714536) * 10 ^ 70 +
        5265550341617533741121373839558551676670734561521046215478975329932624) * 10 ^ 70 +
        0591931501285534474322278517608638941259512479632221061451657007186015) * 10 ^ 70 +
        9307555924650681547700059433926323701796434748963852976533116629991762) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 140 = 22 +
      118 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (268 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_268 :
    recurrence5Scalar1Second.coeff 268 =
      -((((((23 * 10 ^ 70 +
        7433240317734554181541623206096638141856114961295653339296176966904215) * 10 ^ 70 +
        2465919575057743819970595590214290939880973098255705531435588724835801) * 10 ^ 70 +
        6684115961786910298447059662198660040650814466438003028484031000278730) * 10 ^ 70 +
        8664193119681310505169386929102151473513783744327861015986167984249368) * 10 ^ 70 +
        4483355542284783772420532088766404645854004465055508284420299017400493) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 141 = 22 +
      119 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (269 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_269 :
    recurrence5Scalar1Second.coeff 269 =
      ((((((14 * 10 ^ 70 +
        0169335201935102580790607925778752064028403006886378313740091449344966) * 10 ^ 70 +
        6830282203313193707493587988971204374398683957739616511610887856730239) * 10 ^ 70 +
        4086905727156078366317908104558717391689940467326392831925876154269622) * 10 ^ 70 +
        9871005060860246062732549422547327243390140859122740323790256809939296) * 10 ^ 70 +
        7429179788283169035955679734593989032233242500365486610463563370034659) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 142 = 22 +
      120 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (270 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_270 :
    recurrence5Scalar1Second.coeff 270 =
      -((((((6 * 10 ^ 70 +
        3563734331981422976607406501391692486399129374914753559938334299206581) * 10 ^ 70 +
        4678461687452000226518830937813978374951095768316907439054000560635168) * 10 ^ 70 +
        0552776765887611510382867607023573996278637452579348035269415004825857) * 10 ^ 70 +
        4374384511612345296798794355575239434532392402135746120187002608615671) * 10 ^ 70 +
        3447458777863346597212426439030465819423278972171862095282225039977533) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 143 = 22 +
      121 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (271 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_271 :
    recurrence5Scalar1Second.coeff 271 =
      ((((((1 * 10 ^ 70 +
        5070023986997796845079968449824336071468131823521108285736676365351739) * 10 ^ 70 +
        7690608855495635672247848815877266047272688589275717693816840864218395) * 10 ^ 70 +
        5091728679925916178620281270318029689901942935548293502314773338799222) * 10 ^ 70 +
        8209884438891966414503547498741460280452588798851847294318768618206175) * 10 ^ 70 +
        6174948089617174036433910208554376300520330657885029091511835973114242) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 144 = 22 +
      122 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (272 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_272 :
    recurrence5Scalar1Second.coeff 272 =
      ((((((1 * 10 ^ 70 +
        0043029066427330112615620704866310623873033142690865791431558326275871) * 10 ^ 70 +
        9578881632124900441483270361438906028202097055691961106997791318882452) * 10 ^ 70 +
        7208129997774139338456645944848869389662937693886129393128775411531831) * 10 ^ 70 +
        9457327616207971583399883549751291773669892379583211404192270890950393) * 10 ^ 70 +
        2096844970812714781196158191214614428770328775597128466456637540114690) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 145 = 22 +
      123 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (273 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_273 :
    recurrence5Scalar1Second.coeff 273 =
      -((((((1 * 10 ^ 70 +
        9520463730657930762456122546288080490618241245811170566523527305724504) * 10 ^ 70 +
        9834781944436622143272465517231307745530930689022281515210543756229418) * 10 ^ 70 +
        8751955582809251858449945273451911104287884471745871244633660411577165) * 10 ^ 70 +
        4247237334565780081334171565658390484390208332957631969609868513334356) * 10 ^ 70 +
        0945026132984319859838214754949667308293030851174894472792588076708826) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 146 = 22 +
      124 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (274 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_274 :
    recurrence5Scalar1Second.coeff 274 =
      ((((((2 * 10 ^ 70 +
        0220569120837512984592649695201588078365637410174032311772363383820985) * 10 ^ 70 +
        5423362354408243290247326801725204850063950836819447077497050417475733) * 10 ^ 70 +
        0984338249655064870736248120250256039101755097087007308640327949329084) * 10 ^ 70 +
        1685644528394290440403862514726713226631430643487332589706553977989775) * 10 ^ 70 +
        7809964400194681954603815600167482282037471278476728417532092603336901) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 147 = 22 +
      125 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (275 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_275 :
    recurrence5Scalar1Second.coeff 275 =
      -((((((1 * 10 ^ 70 +
        6963152370226966366804169653349210650669414392097474088363076722453571) * 10 ^ 70 +
        4962556171734433233696305528547701895017392793529429505825336661710311) * 10 ^ 70 +
        9225506000163043599589822885001272982188722853253735206637808664878634) * 10 ^ 70 +
        4392834282072553548249469956916667127145541000581722004985564145688392) * 10 ^ 70 +
        5126396932338229448828889062150150405623029914139444374724271609436024) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 148 = 22 +
      126 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (276 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_276 :
    recurrence5Scalar1Second.coeff 276 =
      ((((((1 * 10 ^ 70 +
        2618873042191992062882209943510245550467434698386923758682293203503177) * 10 ^ 70 +
        9822933489840009483475380973505250887147715527228837948344744366595327) * 10 ^ 70 +
        1815024816643383129762242505257392641832954774068700194331611715702927) * 10 ^ 70 +
        0064385822768671622490758649441830005204626723060184076551332127639075) * 10 ^ 70 +
        6334968242346723067369986813702016331706947165007273104987213167604323) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 149 = 22 +
      127 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (277 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_277 :
    recurrence5Scalar1Second.coeff 277 =
      -(((((8619190732514507127175396356182875829301721457273326136044114511887189 * 10 ^ 70 +
        7530935184328786195806163714773524939442325242575590351256321098765787) * 10 ^ 70 +
        6655582173245515607955336715112555158843788821854943668101643829838752) * 10 ^ 70 +
        5470639878440767964913187789813537500400698356503150920762000268957216) * 10 ^ 70 +
        2290937928403379227620780930483841997742011579013467977269118831657868) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 150 = 22 +
      128 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (278 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_278 :
    recurrence5Scalar1Second.coeff 278 =
      (((((5495140391643861964627227576021049800833796576176898526489401896543218 * 10 ^ 70 +
        6083648196949802315122438035216876593594690276805058766366265968119600) * 10 ^ 70 +
        3456380963071807745547500720624223243538119901347697080783817483725968) * 10 ^ 70 +
        5248746393137183556659366478680874048835043356463543929718521012726146) * 10 ^ 70 +
        1075671979762416106410835859921654787653263331767289944950179191564415) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 151 = 22 +
      129 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (279 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_279 :
    recurrence5Scalar1Second.coeff 279 =
      -(((((3296716238857651820400102601493249812748109138026173255052259885680887 * 10 ^ 70 +
        3080084816354494520996431532938513190445112216133126154831439227608211) * 10 ^ 70 +
        9897524800184882877081916546684033628316523955225306811227057521830095) * 10 ^ 70 +
        6516841985223613543888879848603836251867331136082105005108734348781305) * 10 ^ 70 +
        6270747033404420820781531416770260926818399302278835613898859081591117) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 152 = 22 +
      130 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (280 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_280 :
    recurrence5Scalar1Second.coeff 280 =
      (((((1867278365094381065033698219477865291632863475820881279113372036413107 * 10 ^ 70 +
        9619460590062445251894064750342811537538302136158558108348264719822493) * 10 ^ 70 +
        5586337602169755599803468920294229595516963852409378172746604094557722) * 10 ^ 70 +
        7733553470495098367622060908580598190130110143653175398045972089995574) * 10 ^ 70 +
        7193719873732539303823155196706436678771020857368457231220851637837930) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 153 = 22 +
      131 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (281 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_281 :
    recurrence5Scalar1Second.coeff 281 =
      -(((((998174391349510477504148680029187386143116053835859446007611324490592 * 10 ^ 70 +
        1672177641460687083506498870627015936090524936041435106991978424706880) * 10 ^ 70 +
        3739994431722171577939716982917408701097077403598908319653539730691427) * 10 ^ 70 +
        7063923964786394871824463301257063396560339384017020130352561050070614) * 10 ^ 70 +
        5248304761925546429368073552701142079450834672432539978168522867513901) : ℚ) := by
  unfold recurrence5Scalar1Second
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
    rw [show 154 = 22 +
      132 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
