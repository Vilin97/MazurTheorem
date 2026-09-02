/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1SecondPart2Simp
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

private theorem recurrence5Scalar1Second_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (364 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_364 :
    recurrence5Scalar1Second.coeff 364 =
      -(((((37525978086982864393920974132094248621 * 10 ^ 70 +
        8690359751201722667155548630552502718660392124431057976319814306336843) * 10 ^ 70 +
        1468797791274094475621814048863596917800752749784357951648301921051739) * 10 ^ 70 +
        5891593511391084713400668605504251660047955318646018002947876909584076) * 10 ^ 70 +
        2151531520480577295937890225277112250803637055065553441364284275829456) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 365 = 51 +
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
    rw [show 218 = 3 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (365 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_365 :
    recurrence5Scalar1Second.coeff 365 =
      (((((13365716775050078134310239841885281443 * 10 ^ 70 +
        7672660265049383002675138284968990868728424090891081093633668420770048) * 10 ^ 70 +
        6073107754677425192165873728256327955833349574047457819235211646623467) * 10 ^ 70 +
        8518861671848801803309809890884741717008914878897370404046459728428691) * 10 ^ 70 +
        6361636666891890428270060392692545562369354064112647245399830680181100) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 366 = 52 +
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
    rw [show 218 = 2 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (366 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_366 :
    recurrence5Scalar1Second.coeff 366 =
      -(((((4674151394465598712685572171860197454 * 10 ^ 70 +
        7715219156280762838364902055134113717427183068372487051848684016448705) * 10 ^ 70 +
        7014625054071092660632281678008568799641908838846711105023766839522346) * 10 ^ 70 +
        2791736557992407157360834652780084063444460620051238387585977700632152) * 10 ^ 70 +
        2743972010550815801843537251407424759905519045077385124932911228463751) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 367 = 53 +
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
    rw [show 218 = 1 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (367 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_367 :
    recurrence5Scalar1Second.coeff 367 =
      (((((1602639913420459044336721490686357417 * 10 ^ 70 +
        3205053384229062927347931497288725249975079531333261418901462006990374) * 10 ^ 70 +
        0000240751793791215545283298765895444422477240085228422321110166620463) * 10 ^ 70 +
        2977802512861345078634123181143612931239459547701766597912405946740892) * 10 ^ 70 +
        6443626686804430698495989053472479344338151353015377575946165169063842) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 368 = 54 +
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
  rw [recurrence5Scalar1Second_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (368 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_368 :
    recurrence5Scalar1Second.coeff 368 =
      -(((((537852048902660032845417987066684592 * 10 ^ 70 +
        1387692693119430950620998834191581799897477842584739049469506423140109) * 10 ^ 70 +
        9697732668797595368711268098536299523880645116680947548341494273030286) * 10 ^ 70 +
        2590904941954668370490725295215603998784308608006683779626821925959645) * 10 ^ 70 +
        9369192643794423949613508508856764285237324190042079695655774029280689) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 369 = 55 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 31 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (369 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_369 :
    recurrence5Scalar1Second.coeff 369 =
      (((((176400054624583950266982696689191361 * 10 ^ 70 +
        5356826271061102582262756533318330430282719673198405525982742258517343) * 10 ^ 70 +
        7102387221269959521450098546377959022590353955109500023540486463380158) * 10 ^ 70 +
        9108430814572515222025480045946040549717693636544400330959937837324812) * 10 ^ 70 +
        0014064725344112129247255960729220949196403513930073271409812013496576) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 370 = 56 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 30 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (370 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_370 :
    recurrence5Scalar1Second.coeff 370 =
      -(((((56464294703806705036799124274521534 * 10 ^ 70 +
        9897313018481863290002438095786593708561536548338012343102049688228330) * 10 ^ 70 +
        5147430557530045389581006126247555954030086053719681265035804423925065) * 10 ^ 70 +
        2969595177110289619492331654646333372516839744900830184872198809159942) * 10 ^ 70 +
        5285372629358695276739025121873874510253422544182811067985263874618247) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 371 = 57 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 29 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (371 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_371 :
    recurrence5Scalar1Second.coeff 371 =
      (((((17621041641962547134012126218251018 * 10 ^ 70 +
        3823485565959483149294167249893244509744559817593337496412786502019118) * 10 ^ 70 +
        2092449702069980039603896269644812790249425897546175085197530884480583) * 10 ^ 70 +
        6044346975194012541362394001205944307616924381719582591433229868227980) * 10 ^ 70 +
        4575013689167709396414324982594433035235395682867664468375097456039320) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 372 = 58 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 28 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (372 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_372 :
    recurrence5Scalar1Second.coeff 372 =
      -(((((5356199976633219633188466639439497 * 10 ^ 70 +
        1583921669589472758217369368351367701247670293628658270152859339028540) * 10 ^ 70 +
        1818583469669811669913611347652335500848788744769769302819342597481498) * 10 ^ 70 +
        2699186172243943997523930734231419857892146480645656261671791461679194) * 10 ^ 70 +
        5002858075700050346518073924117793304741504456725905964484366892162512) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 373 = 59 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 27 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (373 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_373 :
    recurrence5Scalar1Second.coeff 373 =
      (((((1583947191899266808528887849637677 * 10 ^ 70 +
        4901244632733469901657907006204569042921695199995099359846666543814891) * 10 ^ 70 +
        4235277248673236314164233941263765455779217432884834066703331975820022) * 10 ^ 70 +
        7931178749209376775405804690587175019519398454801388742622704377566148) * 10 ^ 70 +
        1183965421552428324572530257773381839384981079377146881337192615758642) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 374 = 60 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 26 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (374 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_374 :
    recurrence5Scalar1Second.coeff 374 =
      -(((((454867000126279374899851585224020 * 10 ^ 70 +
        5783084763872593326737236075381776263114797517963341740452248436017827) * 10 ^ 70 +
        3165548465274319097906477039632691568363421357847998184731375107714214) * 10 ^ 70 +
        3772863215211576614620603462370546523573107246406660297670345197130988) * 10 ^ 70 +
        8394488132333172005950845894883021578168643841432578946617906399838877) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 375 = 61 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 25 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (375 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_375 :
    recurrence5Scalar1Second.coeff 375 =
      (((((126457224940304577388967679197073 * 10 ^ 70 +
        9159611877009316694774940227654692219480517112136493610633558018778055) * 10 ^ 70 +
        5199706173400147870510842169072413546690984858692226968134518689949306) * 10 ^ 70 +
        2486558769947469627855379008967175377161813532563102817757137601411272) * 10 ^ 70 +
        2169711977692388079966860165161039941609572821901627795630753078660893) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 376 = 62 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 24 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (376 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_376 :
    recurrence5Scalar1Second.coeff 376 =
      -(((((33860750183569295977427278488258 * 10 ^ 70 +
        8354036006665164356207827614517292020056080383665168171713081522320503) * 10 ^ 70 +
        5751541054841813224635210498841090513738530474479697688053476332918987) * 10 ^ 70 +
        0091917604319060220493682386446191191774976604315428691378997522359930) * 10 ^ 70 +
        0825996873519041652570954792598332971307083123403388202040608151714006) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 377 = 63 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 23 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (377 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_377 :
    recurrence5Scalar1Second.coeff 377 =
      (((((8660764759943047806297575350365 * 10 ^ 70 +
        8597614503838316292873439823010521973061309976684410735891635616796472) * 10 ^ 70 +
        3233575941609554244767022219110721720581293205276574657708328663757894) * 10 ^ 70 +
        3618112084369199174115970270232837522178099354223382821026742700214713) * 10 ^ 70 +
        6531436983901549656420640453359874675823389585128644304012783895927228) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 378 = 64 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 22 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (378 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_378 :
    recurrence5Scalar1Second.coeff 378 =
      -(((((2087719818617139746889068801310 * 10 ^ 70 +
        0152467943320858260751268979961256999967595719352586447338850030607634) * 10 ^ 70 +
        0876255423108446308255497657197051693557831732646622885226167694939043) * 10 ^ 70 +
        4786370970779348988258051785255292228240635902153740015126807915913305) * 10 ^ 70 +
        7663828488338488042791741349227807355087565668049649911668242221906156) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 379 = 65 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 21 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (379 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_379 :
    recurrence5Scalar1Second.coeff 379 =
      (((((463257503066383916589028531635 * 10 ^ 70 +
        2958807464495856811962514076236661423752357451783450066255998786514040) * 10 ^ 70 +
        4551125444036365308398064099155605492425789869768441592582763998018151) * 10 ^ 70 +
        0650992280423385886936682185056004634092471158823142292710865977666548) * 10 ^ 70 +
        0518520766653746612734232050306032524658915579822499987027013272069699) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 380 = 66 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 20 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (380 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_380 :
    recurrence5Scalar1Second.coeff 380 =
      -(((((90179324056750792394800554877 * 10 ^ 70 +
        1259917491401967280290370258618727415280151790668600927334367350852268) * 10 ^ 70 +
        5722398216944735118329813458307486080561961281640268315053583620429049) * 10 ^ 70 +
        7244570064561717126557024149418054145668098323811307283194042772386785) * 10 ^ 70 +
        9645028430021938489940316718880779862411248658119829736442927930152190) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 381 = 67 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 19 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (381 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_381 :
    recurrence5Scalar1Second.coeff 381 =
      (((((13451153218769368152701330305 * 10 ^ 70 +
        2498539643424592735168360987069423804390935448417196586298434365275232) * 10 ^ 70 +
        7053031211441310214871544899975135957125565872877503714148154184468838) * 10 ^ 70 +
        3972206350464608891299931615478686536327143062571462008010504426988286) * 10 ^ 70 +
        3435822450656866983688510459976427589279446292990120806715000850699654) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 382 = 68 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 18 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_381_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (382 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_382 :
    recurrence5Scalar1Second.coeff 382 =
      -(((((544462701116959005804664651 * 10 ^ 70 +
        8565573361452120413659041063231365064928717506367562195310590821490110) * 10 ^ 70 +
        9440112889087194932418942570153839545638778115787828364830274097112317) * 10 ^ 70 +
        9446322415598993366451545962042989394009568369218196052268155493514807) * 10 ^ 70 +
        6829149990093993921177440415056594981673845281430623139499989418998383) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 383 = 69 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 17 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_382_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 234,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (383 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_383 :
    recurrence5Scalar1Second.coeff 383 =
      -(((((644116348599474844478487319 * 10 ^ 70 +
        1544361110536105429319694351568392279395994795699971898650901598110581) * 10 ^ 70 +
        8485473745946316124494254279053166595669977105825517903727010971590439) * 10 ^ 70 +
        8516498219788782659079822924824018185204081184916054214197306928119344) * 10 ^ 70 +
        0375329337915871566983145031071045809171995291061858012131330654262845) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 384 = 70 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 16 +
      234 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_383_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (384 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 235,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (384 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_384 :
    recurrence5Scalar1Second.coeff 384 =
      (((((354264410240058813541405511 * 10 ^ 70 +
        1918456440551465236944850337869132319193540582693794341700870846480026) * 10 ^ 70 +
        4697137118163547537559721780037408317167067070094986424806138023055780) * 10 ^ 70 +
        7710029494262180968003109385223246170104656080691150872882791881419356) * 10 ^ 70 +
        0750628347606344003270394660568440360668911574296372568497755887809172) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 385 = 71 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 15 +
      235 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_384_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (385 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 236,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (385 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_385 :
    recurrence5Scalar1Second.coeff 385 =
      -(((((130688961226715617891025752 * 10 ^ 70 +
        1510504898939481973972265880223755928487335719075605269847363319554068) * 10 ^ 70 +
        0266947918828393086401628283764370382932288596648552411344007457329759) * 10 ^ 70 +
        6637198543743196873766732955235422109433372982644715505249307673865120) * 10 ^ 70 +
        8576638397853608885912084654823395634916050316704460669844956188688058) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 386 = 72 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 14 +
      236 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_385_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (386 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 237,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (386 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_386 :
    recurrence5Scalar1Second.coeff 386 =
      (((((40360568659064846019242323 * 10 ^ 70 +
        9614342502953798092005925489303398623646703267990799077710288824586683) * 10 ^ 70 +
        5591541561856932981365351077574629868941288742085989297264164725286202) * 10 ^ 70 +
        8606255318277928489758062493695594484383234943044100854845159712647285) * 10 ^ 70 +
        2158235219654717894095036140799386987175400607393213034614182547262395) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 387 = 73 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 13 +
      237 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_386_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (387 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 238,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (387 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_387 :
    recurrence5Scalar1Second.coeff 387 =
      -(((((11077839520353067078683007 * 10 ^ 70 +
        1936158100442460564661430181875786026424713136630246727420031685987258) * 10 ^ 70 +
        1017506661551250142903825764956902578517280917254553085471473242010917) * 10 ^ 70 +
        5598995358313797490716446898356853458579762113057659860036528550196101) * 10 ^ 70 +
        4320372495525063235922827253051224217310282778459899266538369178786154) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 388 = 74 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 12 +
      238 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_387_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (388 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 239,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (388 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_388 :
    recurrence5Scalar1Second.coeff 388 =
      (((((2763690244750753788630817 * 10 ^ 70 +
        6371303589924219590796426222306878260313087360581292857903639428433323) * 10 ^ 70 +
        4429358972005878313764633417727460838563142111863973427858788643051371) * 10 ^ 70 +
        1375791501775390921406572904906727863703012494668315281981814392804230) * 10 ^ 70 +
        7915442859820365685784114428049866527829751988685107588381030474876382) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 389 = 75 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 11 +
      239 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_388_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (389 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 240,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (389 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_389 :
    recurrence5Scalar1Second.coeff 389 =
      -(((((631789220490667313166307 * 10 ^ 70 +
        1878923532974709082632856978513086481225816526152296632052232618404193) * 10 ^ 70 +
        8387906692803803845832248733428725903402857914243805643267434029724439) * 10 ^ 70 +
        6946679937461435061840902837224173805061911237652408657443876100452544) * 10 ^ 70 +
        6051415263006743569666913018774991479469138950908081915341757955648098) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 390 = 76 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 10 +
      240 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_389_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (390 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 241,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (390 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_390 :
    recurrence5Scalar1Second.coeff 390 =
      (((((132365431021471726483740 * 10 ^ 70 +
        7413750246311313975188261157726636682742659909800975947830614558661555) * 10 ^ 70 +
        2098533903730847518167699525602258058510013779397727871171921624962018) * 10 ^ 70 +
        9775902565299568997181334069780952616674589378050566759605061977434141) * 10 ^ 70 +
        2330598498554298848522649831372682753953507251157572800427838136185288) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 391 = 77 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 9 +
      241 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_390_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (391 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 242,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (391 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_391 :
    recurrence5Scalar1Second.coeff 391 =
      -(((((25246273425979250602954 * 10 ^ 70 +
        8078612227337271672104423793734207213955817538678363342851135425159712) * 10 ^ 70 +
        3689296786576813688474986926079566501096148095309843016963369601647915) * 10 ^ 70 +
        5628359690767313066180124270787322238551771670563460810058381898232392) * 10 ^ 70 +
        2141744885637420086541710510129953626294214216611643198931744738284892) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 392 = 78 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 8 +
      242 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_391_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (392 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 243,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (392 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_392 :
    recurrence5Scalar1Second.coeff 392 =
      (((((4306322911080836255257 * 10 ^ 70 +
        0246192694983262906388340132083197190720609596413108739872705828513234) * 10 ^ 70 +
        4631785547872230160146690793592187661462074952743252814231648983480683) * 10 ^ 70 +
        6549349939653922197947504663717169266693903333650231864477465236438307) * 10 ^ 70 +
        6193106904774356862655110026596568454209173799435396670605425999335836) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 393 = 79 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 7 +
      243 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_392_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (393 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 244,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (393 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_393 :
    recurrence5Scalar1Second.coeff 393 =
      -(((((625001896574431310730 * 10 ^ 70 +
        2956304912016078735337340688309428128344390757424222762775789881683703) * 10 ^ 70 +
        6122945099102204895987929329626789668186416692379104782410594196085231) * 10 ^ 70 +
        6523411834414321761306673995902500672364300957696081477180369154804761) * 10 ^ 70 +
        5142269806772457311413675967109549829380070644817458806401223643949147) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 394 = 80 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 6 +
      244 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_393_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (394 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 245,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (394 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_394 :
    recurrence5Scalar1Second.coeff 394 =
      (((((63142659176846400253 * 10 ^ 70 +
        7541092504992808897037078886041413526338698468272313551062500310943626) * 10 ^ 70 +
        9368232256760643756220135144338553120687639712339896839742484181060241) * 10 ^ 70 +
        9458511547933690801580220420875785612771818827098134242918594804056133) * 10 ^ 70 +
        4749248592833199834399045655942688160390953143708534004213019510563567) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 395 = 81 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 5 +
      245 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_394_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (395 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 246,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (395 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_395 :
    recurrence5Scalar1Second.coeff 395 =
      (((((2546085860401682891 * 10 ^ 70 +
        8441157837407486512472149300441705789913129269136061407309088365920021) * 10 ^ 70 +
        6815988639282288950544482761597743256520986824997946101618771824109501) * 10 ^ 70 +
        9580935259340781055720837761752874181124788410228281531772170300709508) * 10 ^ 70 +
        6143352242390506705449907288573284122462484520148688143253776011764317) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 396 = 82 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 4 +
      246 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_395_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (396 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 247,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (396 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_396 :
    recurrence5Scalar1Second.coeff 396 =
      -(((((4203610174483292306 * 10 ^ 70 +
        1420385624270934319202877892635703182362048296291822329511273693305804) * 10 ^ 70 +
        0004048915167203602798686020824630463936449136585483623197805251720368) * 10 ^ 70 +
        3216351928420479541056226531959601007613293281094072656600842410934270) * 10 ^ 70 +
        3714559534928452171125375764203710158778345594731390643227159713216465) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 397 = 83 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 3 +
      247 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_396_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (397 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 248,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (397 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_397 :
    recurrence5Scalar1Second.coeff 397 =
      (((((1723598250332477047 * 10 ^ 70 +
        6344424854108451300433222850002405942068744003767964360923617611950958) * 10 ^ 70 +
        6304787855850212375385080187887633169340611202782150772891810476699305) * 10 ^ 70 +
        8840083349651745104030442949567250541970950233652276931963056334704704) * 10 ^ 70 +
        3574514526983818448979632032099603905991767009782191326487092832394676) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 398 = 84 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 2 +
      248 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_397_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (398 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 249,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (398 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_398 :
    recurrence5Scalar1Second.coeff 398 =
      -(((((538076222809929592 * 10 ^ 70 +
        7674710779848930846780218408012899573070148046504856314244806827146349) * 10 ^ 70 +
        9369180765784934075260948672408831266463800170009183155589229608842805) * 10 ^ 70 +
        0043949673242939771890425500737508728770652919735326619455979351142843) * 10 ^ 70 +
        6488629556058207732607245137268579026881380612223734486790972275171957) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 399 = 85 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 1 +
      249 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_398_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (399 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 250,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (399 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_399 :
    recurrence5Scalar1Second.coeff 399 =
      (((((142242346723802478 * 10 ^ 70 +
        8531204611529529512288931144895646359924144941414472831219644246107134) * 10 ^ 70 +
        6776747005895891159009837094784691611234779629197046508124722653918329) * 10 ^ 70 +
        0202249045612000517932545182246865501373295880185122117225278585962735) * 10 ^ 70 +
        3779747327526097291181184945077758316844344044179868672739970941233941) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 400 = 86 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_399_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (400 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 251,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (400 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_400 :
    recurrence5Scalar1Second.coeff 400 =
      -(((((32249620084993739 * 10 ^ 70 +
        8137437532593050909518812635510026657105273716526547078805843822983557) * 10 ^ 70 +
        8137217625925287774202721956250224953136926580249015889946980233279457) * 10 ^ 70 +
        6846724573514254820645435576848207461187874474179187016053363616139651) * 10 ^ 70 +
        5547008351860372591997975648927019168307720900270429155272423985537620) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 401 = 87 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 31 +
      251 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_400_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (401 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 252,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (401 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_401 :
    recurrence5Scalar1Second.coeff 401 =
      (((((6147502575822385 * 10 ^ 70 +
        3248135195549050315296308346325506121020380256122115004833487471463922) * 10 ^ 70 +
        4013077765644315252950524512849361211342169694248764692974783543782285) * 10 ^ 70 +
        1151684447298266798204349085242237940923280307620969500179771080004475) * 10 ^ 70 +
        3371709778024910346992973765119202977544986289410442082809047863535136) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 402 = 88 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 30 +
      252 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_401_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (402 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 253,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (402 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_402 :
    recurrence5Scalar1Second.coeff 402 =
      -(((((928000764801456 * 10 ^ 70 +
        5211860111111986165797362360578032581662473788559179692805094038947625) * 10 ^ 70 +
        7276663913963315390459031883013391221050974402807539604210029481824450) * 10 ^ 70 +
        8011931088420636019967245287309539995712054797701725393320825890920098) * 10 ^ 70 +
        8670200114449738199499870010165235954946398161387827223488603779941376) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 403 = 89 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 29 +
      253 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_402_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (403 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 254,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (403 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_403 :
    recurrence5Scalar1Second.coeff 403 =
      (((((89925223896630 * 10 ^ 70 +
        5838936810523574385875743787563761499228261050348216707875335519123328) * 10 ^ 70 +
        1120000394944172658840378958943041927336686745978289480424165233207887) * 10 ^ 70 +
        3404311497825819658854969119725779533236476437346184424243450602514898) * 10 ^ 70 +
        3075026714925510952018542444560008404481320378496996305285776362320636) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 404 = 90 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 28 +
      254 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_403_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (404 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 255,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (404 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_404 :
    recurrence5Scalar1Second.coeff 404 =
      (((((2624439823226 * 10 ^ 70 +
        6870474417990515330169876865478224861273732150530465605584148144324349) * 10 ^ 70 +
        9351739183048515203245372639291651476734497756434206642739203114680091) * 10 ^ 70 +
        6975594582793757416966486489611965222072643017634955397604394725782935) * 10 ^ 70 +
        9384593767647706499300187732213525784177570142340766621841320989229461) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 405 = 91 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 27 +
      255 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_404_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (405 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (405 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_405 :
    recurrence5Scalar1Second.coeff 405 =
      -(((((3724538411379 * 10 ^ 70 +
        8497629252103536723328059327234841779703581277127849241951733968467830) * 10 ^ 70 +
        0489395301176031759549334115932875499473115275373973320602900022223068) * 10 ^ 70 +
        7806967380788951955452997627988971333895843119738421709292481422336525) * 10 ^ 70 +
        3296744006937672957671767827597102020459934068752731520646973954556425) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 406 = 92 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 26 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_405_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (406 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 257,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (406 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_406 :
    recurrence5Scalar1Second.coeff 406 =
      (((((1052613364309 * 10 ^ 70 +
        5274096137882947458917026102440134774669319678907541675943152960394191) * 10 ^ 70 +
        5170455761139440462335044700131999169027341427678848298924672397923005) * 10 ^ 70 +
        6951940542490462117627965496749003117957189960202022346581355548019461) * 10 ^ 70 +
        6021971043176446860002149146079414824418726544755430088060636336686560) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 407 = 93 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 25 +
      257 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_406_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (407 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 258,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (407 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_407 :
    recurrence5Scalar1Second.coeff 407 =
      -(((((206118739248 * 10 ^ 70 +
        5662848230004144429041755215379708949991451534834177680950855761167455) * 10 ^ 70 +
        0495035651224648424489401831309236473276903396492781087626385275826047) * 10 ^ 70 +
        6799381818120469463943952535653659128924884097116665959715577985670689) * 10 ^ 70 +
        4631441655695692008407742039836081196569363960185450529026260359798508) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 408 = 94 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 24 +
      258 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (408 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 259,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (408 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_408 :
    recurrence5Scalar1Second.coeff 408 =
      (((((31919791185 * 10 ^ 70 +
        0915632698120804235144108088434020411361876852816143003199236253659309) * 10 ^ 70 +
        4278014585240219561939972336878735026238296492461696964000548197502029) * 10 ^ 70 +
        8290128612026531041007818781293675434437386402449749422751179512454650) * 10 ^ 70 +
        2409507735527499126618332809371825600590208023534709926110890528207524) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 409 = 95 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 23 +
      259 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (409 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 260,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (409 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_409 :
    recurrence5Scalar1Second.coeff 409 =
      -(((((4036306560 * 10 ^ 70 +
        9031820019341245873509065598354664208145448922269173914666172556921253) * 10 ^ 70 +
        4471095412823693131730728860678079984838750344795984767360733213358237) * 10 ^ 70 +
        3991576764136983360146516343511835657580765475964479362227676025401481) * 10 ^ 70 +
        3362780580066992983806336886187192141318862516808275516699467848556857) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 410 = 96 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 22 +
      260 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (410 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 261,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (410 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_410 :
    recurrence5Scalar1Second.coeff 410 =
      (((((409583993 * 10 ^ 70 +
        1897536786802909519031233186405001132298114792000445987604764126117780) * 10 ^ 70 +
        7703655833288691154231975486409830225829383560697772481254817424335614) * 10 ^ 70 +
        4023317071079182512734631060256293447073542861825663292248221964442911) * 10 ^ 70 +
        4431362729857967399874963827093456587162329121036954842517896401386622) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 411 = 97 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 21 +
      261 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (411 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 262,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (411 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_411 :
    recurrence5Scalar1Second.coeff 411 =
      -(((((29034614 * 10 ^ 70 +
        5582084028338004947308409421900098627665427558912330388708384527110158) * 10 ^ 70 +
        0310066005528132391305410415582597389268337272443563973187142861058948) * 10 ^ 70 +
        5813351821387516128736275525237913132716570214966891747747809413706156) * 10 ^ 70 +
        8550754193628652519783890357063290454144569832646862690112463919833006) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 412 = 98 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 20 +
      262 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (412 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 263,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (412 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_412 :
    recurrence5Scalar1Second.coeff 412 =
      (((((30259 * 10 ^ 70 +
        4239069136308898615660735261565354537425190085638529307969099481140823) * 10 ^ 70 +
        8778281827534345217581406673910427900964977882003009249259023620559624) * 10 ^ 70 +
        9402656394253550225809309928550529633932229120681193268812948774581452) * 10 ^ 70 +
        2685592643922678275927416771306479643595473995871138823983809129383831) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 413 = 99 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 19 +
      263 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (413 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 264,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (413 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_413 :
    recurrence5Scalar1Second.coeff 413 =
      (((((486340 * 10 ^ 70 +
        0704659188777361422027010118010597438121408522756475891464086545564606) * 10 ^ 70 +
        4383830563284450558734516563131062148347024791146774873884888851191621) * 10 ^ 70 +
        6242227649107740112834813503651416386777916325497997627196520780599610) * 10 ^ 70 +
        8545213821404292782332484588061687810633341917643177476568933309697293) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 414 = 100 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 18 +
      264 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (414 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 265,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (414 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_414 :
    recurrence5Scalar1Second.coeff 414 =
      -(((((114646 * 10 ^ 70 +
        5400537930063951837836586943176335470404795485768461224228693074099874) * 10 ^ 70 +
        3622956403773297133119775239987744710112251899219571562370651982329450) * 10 ^ 70 +
        7435673851470457239205208075229535922136162562203482343482718025168764) * 10 ^ 70 +
        5749380314905425840118719238700239000405370147545828897606725912414876) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 415 = 101 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 17 +
      265 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (415 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 266,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (415 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_415 :
    recurrence5Scalar1Second.coeff 415 =
      (((((17678 * 10 ^ 70 +
        3910077538200424816625583485260262470074723825462001335681325965098295) * 10 ^ 70 +
        4558768037414348465836482193885505954340524465082272707867337329170187) * 10 ^ 70 +
        5232645215429448139056001971880237140503984048121434246357340081972865) * 10 ^ 70 +
        9965550358016848271480385916495180626553175694794903748743539072130315) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 416 = 102 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 16 +
      266 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (416 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 267,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (416 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_416 :
    recurrence5Scalar1Second.coeff 416 =
      -(((((1922 * 10 ^ 70 +
        9527721038990468435393264285641188822382184630115346598638034561923420) * 10 ^ 70 +
        8621946321493431080872454158213001479391023147830650427714362046171217) * 10 ^ 70 +
        1322397138488399447493395900211425882811047280199840106346816300285514) * 10 ^ 70 +
        2778103602769300560430831891146552219814793632304880035917773773714649) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 417 = 103 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 15 +
      267 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (417 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 268,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (417 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_417 :
    recurrence5Scalar1Second.coeff 417 =
      (((((119 * 10 ^ 70 +
        8927473702025746473264940337330881865698244173471237014199402330522533) * 10 ^ 70 +
        2331921701489764279547933410606600808476584969304413020997262351220704) * 10 ^ 70 +
        3346541758761643483662454495886697497813881340043056231990457310671388) * 10 ^ 70 +
        6704406819870355373635387272362567952572859136524582965874926920587561) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 418 = 104 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 14 +
      268 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (418 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 269,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (418 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_418 :
    recurrence5Scalar1Second.coeff 418 =
      (((((3 * 10 ^ 70 +
        2985783743450366532054745990628293081112302595607164171131594025400217) * 10 ^ 70 +
        4126097594256340734620749145731017464042893170383361048652062007966003) * 10 ^ 70 +
        9879367087472723141856619121114098509744919193181545575189539440829821) * 10 ^ 70 +
        8013076038441287719058663128264798778421257411618242511195074587417190) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 419 = 105 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 13 +
      269 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (419 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 270,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (419 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_419 :
    recurrence5Scalar1Second.coeff 419 =
      -(((((1 * 10 ^ 70 +
        8572551378115577388376276525866610397145251143040205102239812721127536) * 10 ^ 70 +
        1724289001128209729928677893838832968396590203021162614121622046253955) * 10 ^ 70 +
        8800634632326990430365002698364403861610497085932240259735184247899074) * 10 ^ 70 +
        1804634623492521509907924858034942810339001930411179127194088939323292) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 420 = 106 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 12 +
      270 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (420 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 271,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (420 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_420 :
    recurrence5Scalar1Second.coeff 420 =
      ((((2337032044777446731937976125699128691202156504205728227726706004270936 * 10 ^ 70 +
        6604105187698336555817984077512646527061452099516027763547550697176728) * 10 ^ 70 +
        5691827778329608298926199762026054766132011651635384705222617216488113) * 10 ^ 70 +
        5822890454766111453355912272485785616550646354316724710166540462233691) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 421 = 107 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 11 +
      271 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (421 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 272,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (421 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_421 :
    recurrence5Scalar1Second.coeff 421 =
      -((((145986798323267589889758660144238254222932936073978627575669215188249 * 10 ^ 70 +
        3155117166028066190532023816208385442085102116632919996837338898097621) * 10 ^ 70 +
        9730804161030585923623782230474182964949401446809620975391795245738568) * 10 ^ 70 +
        7388576094182129547092651584592807689687066323909762895794965123163442) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 422 = 108 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 10 +
      272 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (422 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 273,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (422 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_422 :
    recurrence5Scalar1Second.coeff 422 =
      ((((489524836524388701918674259103207676930232780117288661307643639118 * 10 ^ 70 +
        9251580938377885903241050515937160263087364983464361907814796896714918) * 10 ^ 70 +
        9249486477367926665617426417166369203486361895913256039465194470692000) * 10 ^ 70 +
        9178931318062052091078793146658738529937933268193850239674744163141150) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 423 = 109 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 9 +
      273 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (423 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 274,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (423 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_423 :
    recurrence5Scalar1Second.coeff 423 =
      ((((751029422077030210382255768427002036787015617388958623172652863194 * 10 ^ 70 +
        0026840644584619914415149295747414780127605016723511587188666316943557) * 10 ^ 70 +
        3062135327429879478265087611378583339291313052185158586588171388357553) * 10 ^ 70 +
        7219328318888913016260504384178919675921079063401040308330549870512386) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 424 = 110 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 8 +
      274 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (424 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 275,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (424 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_424 :
    recurrence5Scalar1Second.coeff 424 =
      -((((61484123836754390247341595656107576543255027784030184511370970435 * 10 ^ 70 +
        5436794091287595426986397680041564381868141215067082422891780871320808) * 10 ^ 70 +
        9177286059635274149392622378880106087341352966014697546371256796360747) * 10 ^ 70 +
        3872145936919812215048122088168499823550863267004868344103924847292909) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 425 = 111 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 7 +
      275 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (425 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 276,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (425 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_425 :
    recurrence5Scalar1Second.coeff 425 =
      ((((1303715208332487237740832195689042570038685627401333484433774992 * 10 ^ 70 +
        8419589597799118446317447215186089510958478333607893805823563078195060) * 10 ^ 70 +
        5628931320755918074307756466251626396238616395752641822745349953116832) * 10 ^ 70 +
        7379683585352727979199462496426594244230140789613897236066932131692577) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 426 = 112 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 6 +
      276 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (426 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 277,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (426 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_426 :
    recurrence5Scalar1Second.coeff 426 =
      ((((105502771259798026245952615212735758480074871701444610891453225 * 10 ^ 70 +
        6788466965457918883299909775639407213355755840964956937298488571019560) * 10 ^ 70 +
        6792505375563917624052806174508397761826936793431853779665198411261181) * 10 ^ 70 +
        4719368003409295115278771980333512733228820142205770312271759131080937) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 427 = 113 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 5 +
      277 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (427 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 278,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (427 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_427 :
    recurrence5Scalar1Second.coeff 427 =
      -((((6700575332663738084518306801279973224255812268441993510059938 * 10 ^ 70 +
        8811802315250544601817797182620641665875203279707684738254661512854629) * 10 ^ 70 +
        5499570514124637826144401145368764609794470484271562842652732802812391) * 10 ^ 70 +
        7863915938736279593471049676723697245422907973116097262053296180918848) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 428 = 114 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 4 +
      278 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (428 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 279,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (428 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_428 :
    recurrence5Scalar1Second.coeff 428 =
      -((((15783709459766790389125483353806112777172151640748193228702 * 10 ^ 70 +
        1586475157102899776838366432179954102872603537520844879386683658674430) * 10 ^ 70 +
        0994369285351797553017402559172323882010003279039078031286255752340957) * 10 ^ 70 +
        3954053719779742433651152039389060764791168227823449696618604433174129) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 429 = 115 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 3 +
      279 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (429 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 280,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (429 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_429 :
    recurrence5Scalar1Second.coeff 429 =
      ((((8975661245598978195825408370014547084738930259855429931077 * 10 ^ 70 +
        7987324187806359195696154934756200069024088361018686515450599299329363) * 10 ^ 70 +
        6522800857689266788272516769647907591435036657670378003037891697989898) * 10 ^ 70 +
        6106643644652329611292576572220696459825952178083264753034001582632292) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 430 = 116 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 2 +
      280 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (430 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 281,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (430 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_430 :
    recurrence5Scalar1Second.coeff 430 =
      -((((16766021214990337481725218332761824821351986387802065510 * 10 ^ 70 +
        4746230931335022491521139789408644309005604314040704672193072059672040) * 10 ^ 70 +
        3927009253771171880831829279325527764070597361895722246699644289044141) * 10 ^ 70 +
        1609972038743449439368892840045455592917093382666643304620511194313899) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 431 = 117 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 1 +
      281 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (431 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (431 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_431 :
    recurrence5Scalar1Second.coeff 431 =
      -((((6290680971588695933805120843908515604547464267408900875 * 10 ^ 70 +
        6457612557018662624871158038676215166414181763864718274082085505277806) * 10 ^ 70 +
        1615208481092750884534789981304726460292008521762081581728019910530733) * 10 ^ 70 +
        5535532025347396305297506178598629460824570648583266559365255891562830) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 432 = 118 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (432 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 283,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (432 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_432 :
    recurrence5Scalar1Second.coeff 432 =
      -((((74035640515196325050783596362906657979690458418782292 * 10 ^ 70 +
        2011959991075328255309323885739587542417444847673373296040306373943088) * 10 ^ 70 +
        8975820204167428837180639733164652578988767601060275380358946167731796) * 10 ^ 70 +
        4505601433770072038441133395072396498097697485679238993285684699645282) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 433 = 119 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 31 +
      283 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (433 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 284,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (433 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_433 :
    recurrence5Scalar1Second.coeff 433 =
      ((((471899182183480067293155299414399823455829381465113 * 10 ^ 70 +
        3787897670030666261942209058473264737075130493045691229330951835709126) * 10 ^ 70 +
        3518217967689412742315339621711862831044195152068860633019206007499963) * 10 ^ 70 +
        9044308387382260363180694261221974836291625049833202916105295093044966) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 434 = 120 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 30 +
      284 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_433_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (434 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 285,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (434 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_434 :
    recurrence5Scalar1Second.coeff 434 =
      ((((14999912010139386475552414817246938658942410522334 * 10 ^ 70 +
        9153179553144030484830759796366323938974891133469849276517681553281692) * 10 ^ 70 +
        3700478103282459160473421208058924031543009479734550388106819350970639) * 10 ^ 70 +
        3462885096922010291111982544357198168663354133070351419600167798607111) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 435 = 121 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 29 +
      285 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_434_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (435 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (435 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_435 :
    recurrence5Scalar1Second.coeff 435 =
      ((((103764666122873221728792217956620440083351871027 * 10 ^ 70 +
        8904823646066435318741771121721682067029038721523191939789918285566534) * 10 ^ 70 +
        3126611024773448736785804461861894778281460451164315995727097509135930) * 10 ^ 70 +
        1935119217390595915517082654091825856074414294869277159591545551053193) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 436 = 122 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 28 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_435_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (436 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (436 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_436 :
    recurrence5Scalar1Second.coeff 436 =
      ((((82151852777307722234465762859566010539899226 * 10 ^ 70 +
        2324793858039545616974863281709544151977686831681109057937323048946092) * 10 ^ 70 +
        7473669531616977864241010203252053826876321418674630217315489639239391) * 10 ^ 70 +
        8530203790792278581534789836561019201023949235824317433257897703424834) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 437 = 123 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 27 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (437 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (437 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_437 :
    recurrence5Scalar1Second.coeff 437 =
      -((((2387981129556407888212623131150141731002366 * 10 ^ 70 +
        7378515588981576274843034095787700746239202264769270457890855167056390) * 10 ^ 70 +
        4706769191296042706747960760958658811085484611440932096713679576685339) * 10 ^ 70 +
        5400392036203014756150560166508418417693898781601427619658620929216780) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 438 = 124 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 26 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (438 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (438 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_438 :
    recurrence5Scalar1Second.coeff 438 =
      -((((10908344025826860099073902077061432635879 * 10 ^ 70 +
        4056903150354626077557430043379876790361722628692134470820587158509584) * 10 ^ 70 +
        9088688744337662909317030026314696684937314134462937749153007364021475) * 10 ^ 70 +
        0786206590619181724130529865467512539735799816262916150074265513578487) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 439 = 125 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 25 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (439 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (439 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_439 :
    recurrence5Scalar1Second.coeff 439 =
      -((((1104900317963517656671839969852985400 * 10 ^ 70 +
        1610614711610154476664449569738486758358949189983022124016559475550557) * 10 ^ 70 +
        9882720396039159475852840315522232560004685223330627468815530643699444) * 10 ^ 70 +
        4535601794573451762739360533469327128267626632554862499200622877283990) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 440 = 126 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 24 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (440 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (440 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_440 :
    recurrence5Scalar1Second.coeff 440 =
      ((((103161770683162883497471832966914948 * 10 ^ 70 +
        9241810114208830438136275180824878065986237956928958788206600672712163) * 10 ^ 70 +
        4256581903652586148099614931047883950857613951880246069192484604430819) * 10 ^ 70 +
        9686194739987419784087432810305340484874761351007563867132412116539350) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 441 = 127 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 23 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (441 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (441 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_441 :
    recurrence5Scalar1Second.coeff 441 =
      ((((185033461036866002843818786636306 * 10 ^ 70 +
        5649240811993843562877237415867341689407066909388771016599419498585800) * 10 ^ 70 +
        4425236942231865966687486619257516272943993890881550819612881480967843) * 10 ^ 70 +
        5964535516724628666728498817370844321825463305373336855710417106725197) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 442 = 128 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 22 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (442 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (442 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_442 :
    recurrence5Scalar1Second.coeff 442 =
      -((((329686324926825929524633481894 * 10 ^ 70 +
        5409839539698158853802750184160902133774850442007354356320173051692084) * 10 ^ 70 +
        0751756904454207630370519368159679408046157323947692732817679590012055) * 10 ^ 70 +
        4840408958027213563264317128675018937174456529156427790587955401773893) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 443 = 129 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 21 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (443 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (443 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_443 :
    recurrence5Scalar1Second.coeff 443 =
      -((((1095530240489824542393605186 * 10 ^ 70 +
        6682765898185640494199378836817097207651100251679673985646625846332872) * 10 ^ 70 +
        3900313713648880291203066986523938904530558522485554599583258088823086) * 10 ^ 70 +
        4142069142706825892436073157180484531852434668340029021535192614218189) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 444 = 130 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 20 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (444 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (444 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_444 :
    recurrence5Scalar1Second.coeff 444 =
      ((((211945396120422287433149 * 10 ^ 70 +
        4172031913958116711609486472821841148230781866851974782392922659077648) * 10 ^ 70 +
        9987056346991226389395780985963963737616108532806157101404763927569069) * 10 ^ 70 +
        9408155685410232603607109273782193680640478771144290945874771233203501) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 445 = 131 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 19 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (445 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (445 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_445 :
    recurrence5Scalar1Second.coeff 445 =
      ((((2532259729441345067040 * 10 ^ 70 +
        8955907200268862529807893464669516379082381473263475841635817384711154) * 10 ^ 70 +
        5636051440884927888861199001109287143262815303536123143306511387653905) * 10 ^ 70 +
        0136024039746424714051422098684873622147788741981879495002731243551917) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 446 = 132 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 18 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (446 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (446 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_446 :
    recurrence5Scalar1Second.coeff 446 =
      ((((695214449980573037 * 10 ^ 70 +
        1290893191203212603558073200908436572849649445005601599448478463926286) * 10 ^ 70 +
        1819047280177914644671194939537000863776863617031222573221854801290390) * 10 ^ 70 +
        8800347665079571753881586490417672113797559542238463106544612751728961) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 447 = 133 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 17 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (447 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (447 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_447 :
    recurrence5Scalar1Second.coeff 447 =
      -((((2189753572861161 * 10 ^ 70 +
        0782813743364623163808698288113447618307364848364932344109639975701409) * 10 ^ 70 +
        3124204876025893685232906311252944337049413556733642602729734582076215) * 10 ^ 70 +
        3135842506741795362195887840001878549203570003081849956537484698064492) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 448 = 134 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 16 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (448 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (448 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_448 :
    recurrence5Scalar1Second.coeff 448 =
      -((((1033690601157 * 10 ^ 70 +
        3942267346166443935946183555683277350251281817215414513913873796388793) * 10 ^ 70 +
        1463609158972797275728210524428510423603894584625543493699824650995654) * 10 ^ 70 +
        9104240268250763605158495108571660967008377989237825857903438647261326) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 449 = 135 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 15 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (449 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (449 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_449 :
    recurrence5Scalar1Second.coeff 449 =
      ((((328958967 * 10 ^ 70 +
        0325257634983126049020226263618316337944979893616182064952270065028037) * 10 ^ 70 +
        5299121770645700423077003672750282645282023255514700704463246249488279) * 10 ^ 70 +
        5560939761604628273166597017320828753140363703072950264431909900793422) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 450 = 136 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 14 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (450 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (450 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_450 :
    recurrence5Scalar1Second.coeff 450 =
      ((((143648 * 10 ^ 70 +
        8649650552158485384135839152399075890866805979345220948031624916119287) * 10 ^ 70 +
        9570236671906010294710501109100335967408448354537304065252595919851432) * 10 ^ 70 +
        1925524087774367040333834001505615824850965907654100107474074111778044) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 451 = 137 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 13 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (451 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (451 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_451 :
    recurrence5Scalar1Second.coeff 451 =
      ((((3 * 10 ^ 70 +
        1088975395594020573526497545932281094838935051193854066162471022284669) * 10 ^ 70 +
        7354015138938369624389541144309448499705257508232797761323615390466681) * 10 ^ 70 +
        9072631489223441423132112537913190679593835099936627708343316046947222) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 452 = 138 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 12 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (452 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (452 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_452 :
    recurrence5Scalar1Second.coeff 452 =
      -(((16975469497143398046956125607031125392438992021034701467168854292705 * 10 ^ 70 +
        3276965951394748974918291700313229323538969628508719177192559697951232) * 10 ^ 70 +
        6746412097722440492945049540048936844712448646905839017920282323053284) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 453 = 139 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 11 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (453 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (453 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_453 :
    recurrence5Scalar1Second.coeff 453 =
      -(((588449350137989434672410989937094925896913052213758525984927473 * 10 ^ 70 +
        1360881410103692238954021266034366550669528845874863981745226224289837) * 10 ^ 70 +
        7915003638596189234297829680357926636852502690874809801891352914649274) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 454 = 140 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 10 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (454 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (454 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_454 :
    recurrence5Scalar1Second.coeff 454 =
      (((7449915615703609305647192473631487364400463288217982949383 * 10 ^ 70 +
        5337330912819434625826983572927232672330670075419110957292391136692906) * 10 ^ 70 +
        8213676258064392774423456099920996809637941804208789083747692437866193) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 455 = 141 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 9 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (455 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (455 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_455 :
    recurrence5Scalar1Second.coeff 455 =
      (((270320214497745849286433969719880405617198061166547622 * 10 ^ 70 +
        4457574514011126132462285761248025834878461353260692991012772416724407) * 10 ^ 70 +
        6823598378491137263592210540590220085044237437070245045224969223632224) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 456 = 142 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 8 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (456 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (456 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_456 :
    recurrence5Scalar1Second.coeff 456 =
      (((362442821782622779655954492424284500521888779856 * 10 ^ 70 +
        0583557624985780163108014031720624580464008815513052658377641894419668) * 10 ^ 70 +
        8867863526341139462091745205700760010435727023541224839834128932734948) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 457 = 143 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 7 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_456_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (457 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (457 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_457 :
    recurrence5Scalar1Second.coeff 457 =
      -(((2793823978994054014607235102087510030140554 * 10 ^ 70 +
        8577989924004319731547820608892000036260915811429281066724251800074898) * 10 ^ 70 +
        1474352184503131890113472520193739921230237649903405146472107667819948) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 458 = 144 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 6 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_457_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (458 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 309,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (458 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_458 :
    recurrence5Scalar1Second.coeff 458 =
      -(((3798438849720718485068271973925205004 * 10 ^ 70 +
        6001317218665199004126772207448809389801731440868345215734635846889110) * 10 ^ 70 +
        7619552924548120907004436390301706641785030794171365565716862712405826) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 459 = 145 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 5 +
      309 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (459 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 310,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (459 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_459 :
    recurrence5Scalar1Second.coeff 459 =
      (((242885276176963737431311399326 * 10 ^ 70 +
        9903615167628272484143608169576279722542529140335165411819489963585219) * 10 ^ 70 +
        2922390982445221426142089415705445088711611030910328401911849370095072) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 460 = 146 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 4 +
      310 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (460 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 311,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (460 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_460 :
    recurrence5Scalar1Second.coeff 460 =
      (((183293941082535337711914 * 10 ^ 70 +
        3102025377965909899586243729559137930647057387924947452912810723270289) * 10 ^ 70 +
        5025514571366975723663674922041062600766870799550898624478261521388740) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 461 = 147 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 3 +
      311 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (461 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 312,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (461 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_461 :
    recurrence5Scalar1Second.coeff 461 =
      (((6024092162891670 * 10 ^ 70 +
        6200543530293598792230497927997852292267178730911947800691806543722232) * 10 ^ 70 +
        6322512178507434590111688241034922556497416154155765676973459179468887) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 462 = 148 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 2 +
      312 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Second_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient1.coeff x * recurrence5QuotientConstant.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (462 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar1Second_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 313,
      remainder6Coefficient1.coeff (150 + x) *
        recurrence5QuotientConstant.coeff (462 - (150 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B1_coeff_high (150 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1Second_coeff_462 :
    recurrence5Scalar1Second.coeff 462 =
      -(((31384708 * 10 ^ 70 +
        9602905931205726039450544587141327852425870431952552294862816577298102) * 10 ^ 70 +
        1719681978585743173386312407904635382753421529180927395709449531731379) : ℚ) := by
  unfold recurrence5Scalar1Second
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 463 = 149 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 1 +
      313 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Second_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1Second_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
