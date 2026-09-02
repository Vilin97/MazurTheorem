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

private theorem recurrence5Scalar1First_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (159 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_159 :
    recurrence5Scalar1First.coeff 159 =
      ((((((5 * 10 ^ 70 +
        9607939367946331642192200163366066075376757434164556092373100499801419) * 10 ^ 70 +
        3477293959570038371084707455569157582972011096168082446433012649023714) * 10 ^ 70 +
        5665471156383416329828731086616865402021886300299364609483451010630502) * 10 ^ 70 +
        0009525501573388325237595632239987867008836229294378215314447814762257) * 10 ^ 70 +
        2245146419012221464653229454837455973318717872714603666108574522337672) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 26 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (160 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_160 :
    recurrence5Scalar1First.coeff 160 =
      -((((((14 * 10 ^ 70 +
        0861247955897046877455419930664509292237301861128548037740368662940044) * 10 ^ 70 +
        0939628854994825288298995333606105027126130014954386019516596383124081) * 10 ^ 70 +
        1870186190812245153655368424517483137251647275788452082162804567749742) * 10 ^ 70 +
        1879076901019900675182066840223134120849830589144313975771911772272965) * 10 ^ 70 +
        2157240041892452977564877322308144001348062617392849183273226716731418) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 33 = 26 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (161 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_161 :
    recurrence5Scalar1First.coeff 161 =
      ((((((32 * 10 ^ 70 +
        6827284871297612203907957185646794899146376012015406725072825939732574) * 10 ^ 70 +
        3006336149687421546852898686305380674883778029101359217299553261862148) * 10 ^ 70 +
        3896325427084349617971707180759782340167382617484950125905000399725324) * 10 ^ 70 +
        1438043127592611772006845477852785176882912383846709818606952839679603) * 10 ^ 70 +
        4219509622513365507514853535869373129620770378556565748204891768954655) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 34 = 26 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (162 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_162 :
    recurrence5Scalar1First.coeff 162 =
      -((((((74 * 10 ^ 70 +
        4578858682342250814600017627085549910697014086998182000842996930979927) * 10 ^ 70 +
        3974210279612068503917952885231856106430077003227760237156667837734085) * 10 ^ 70 +
        1873233435655353543176972187041444535131419221928769872136552426146207) * 10 ^ 70 +
        5858734948553910424710288926655843888437881467154788290205353884960444) * 10 ^ 70 +
        6186696735956803620406229360694233280303095195048624325745634182875089) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 35 = 26 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (163 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_163 :
    recurrence5Scalar1First.coeff 163 =
      ((((((166 * 10 ^ 70 +
        5689120295750373261010188321451625827487352281070481989762298057976552) * 10 ^ 70 +
        1354078684430046331114877365947801376282889618759433217572243755340525) * 10 ^ 70 +
        3916180307711316213200392868278590467746853089059120378438041023514732) * 10 ^ 70 +
        9413695810080050138982594983445692306207966028518486388569949552071741) * 10 ^ 70 +
        0317786917261475139357558050818761121551533421520600009026515605579631) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 36 = 26 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (164 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_164 :
    recurrence5Scalar1First.coeff 164 =
      -((((((365 * 10 ^ 70 +
        9251410512084707464159634831307932686859265129787246450381947908539004) * 10 ^ 70 +
        7978001434514080721223988068280416851587955731519632810455510609123040) * 10 ^ 70 +
        6443024978879020800288016212385253195356495862852080987176420677804078) * 10 ^ 70 +
        0936513397049311343803045561556691579885375959531611922116124422201388) * 10 ^ 70 +
        3285537150050755787989491674809277189920086699973707885500494640310832) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 37 = 26 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (165 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_165 :
    recurrence5Scalar1First.coeff 165 =
      ((((((789 * 10 ^ 70 +
        4575136560907869392820858019814048136235503589274450901984076308467950) * 10 ^ 70 +
        3617411486566632396303875342480386959395068463254094209521330261247209) * 10 ^ 70 +
        7656299534351489422216268727080074531722197886630041194212916967405685) * 10 ^ 70 +
        3072598566343715249172642008915228703492272672249044820347858332958988) * 10 ^ 70 +
        2439400206321785660902076252560197677764428213535809168044255888330497) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 38 = 26 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (166 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_166 :
    recurrence5Scalar1First.coeff 166 =
      -((((((1672 * 10 ^ 70 +
        7291000314921580928528870691479127785332174310215181223712315502779159) * 10 ^ 70 +
        0509877680424287040212017573851423819860886003832429802861699193398502) * 10 ^ 70 +
        0906785796578329431091748037775026338949928600207706259212593825957269) * 10 ^ 70 +
        3562081139034302134631416408331655045433068478663536969819085594336556) * 10 ^ 70 +
        4091933050341154846211850442009845021547554749970809288482533345926977) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 39 = 26 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (167 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_167 :
    recurrence5Scalar1First.coeff 167 =
      ((((((3480 * 10 ^ 70 +
        9988071801944780218699557652908030323984105665055333933748130970914813) * 10 ^ 70 +
        8628567190511288819015087161677402313579691760514437254078679430377200) * 10 ^ 70 +
        5838220932195149812832687079513794029677143487506230215319247016716440) * 10 ^ 70 +
        1342414232885174717695127993192340353774128096504685527971208100367288) * 10 ^ 70 +
        6118532769969056194275464761118169484942241519937788894511348926556456) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 40 = 26 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (168 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_168 :
    recurrence5Scalar1First.coeff 168 =
      -((((((7115 * 10 ^ 70 +
        1419588099408554119007077596218452862376910211929796387707002743446809) * 10 ^ 70 +
        4430383005890541551142308936457690660506776975160944725805773602080234) * 10 ^ 70 +
        3325969589374310154392926619302803689547441714044362289351158728983337) * 10 ^ 70 +
        6154786291763043510319597648228268127868499065075957687858135329936300) * 10 ^ 70 +
        9117822861577423887770289143463289194295926177037090792386630732916361) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 41 = 26 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (169 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_169 :
    recurrence5Scalar1First.coeff 169 =
      ((((((14285 * 10 ^ 70 +
        1119681948198329608574338440620490127591340219496101563628273074983833) * 10 ^ 70 +
        3075584592287473309894159682742152379734571796973608266628968184909006) * 10 ^ 70 +
        7345755287492052003898858811229518165232446146855809182060710418318840) * 10 ^ 70 +
        0877411876947166321493075150951846486867746263450409371704980967622207) * 10 ^ 70 +
        8547260055421104088451076439550021395743630387635788782542625172107208) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 42 = 26 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (170 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_170 :
    recurrence5Scalar1First.coeff 170 =
      -((((((28172 * 10 ^ 70 +
        2789110433875337721236398094779166753201200226785918606490384012154734) * 10 ^ 70 +
        9196324729497086918511378712771921280293199189203646343715802559300068) * 10 ^ 70 +
        0383926119811352539137356335843319807405114310776291290829523297189937) * 10 ^ 70 +
        4212212341963386295645151721540995068940792955260733100760718430455323) * 10 ^ 70 +
        4217765069807526275987163194407810504803134775464049523425251920349516) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 43 = 26 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (171 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_171 :
    recurrence5Scalar1First.coeff 171 =
      ((((((54577 * 10 ^ 70 +
        7116745155057686557354988323358880560270322986845846404382959145802397) * 10 ^ 70 +
        5314751331554255286593874610927022334492853563579640158185382747135348) * 10 ^ 70 +
        1096947366805672380774979500519968936057012193205941458758306254989843) * 10 ^ 70 +
        7380335674704694050004208675232673690642232570404115368581350931866800) * 10 ^ 70 +
        4707454650883082816997459965823268787435607230576211612747704570454754) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 44 = 26 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (172 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_172 :
    recurrence5Scalar1First.coeff 172 =
      -((((((103867 * 10 ^ 70 +
        4120444406562898943513805092639948446924475869618562646864746484283642) * 10 ^ 70 +
        2047547742971358141556015887285109093646693998729906747488323908041908) * 10 ^ 70 +
        1531609576237301013789912259669821490635013842687326777917639246885637) * 10 ^ 70 +
        7685780883208125272645036567324805822226723897063000124207273918038081) * 10 ^ 70 +
        5936342580981876337799580647464805397185082547569413419458997489611646) : ℚ) := by
  unfold recurrence5Scalar1First
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
    rw [show 45 = 26 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (173 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_173 :
    recurrence5Scalar1First.coeff 173 =
      ((((((194190 * 10 ^ 70 +
        6956497336885437109804888986834872975608867979661648011465398526657249) * 10 ^ 70 +
        1474567923994745098653193570420306313847076706693175590877484753279076) * 10 ^ 70 +
        4697324495328301065027326790959958390951816063045400086087375929656242) * 10 ^ 70 +
        3288645981644600486375050609373145967369134520032774367818172576977064) * 10 ^ 70 +
        7807417045885653112587096268804392646128094589566145179015758584436158) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 0 +
    174 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 26 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (174 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_174 :
    recurrence5Scalar1First.coeff 174 =
      -((((((356677 * 10 ^ 70 +
        6720181310788818636164883580741500865602569401646915617236523373220371) * 10 ^ 70 +
        5150479657800583276851428235323812430990994219931693840344089612590148) * 10 ^ 70 +
        9849612104309682906948644540002601095473775406682178350898528979607143) * 10 ^ 70 +
        0824404965986112801502296246361326532228273948460471383177897594024591) * 10 ^ 70 +
        2753363427461576572186328117835663780958866194079180780189873537103470) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 0 +
    175 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 26 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (175 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_175 :
    recurrence5Scalar1First.coeff 175 =
      ((((((643626 * 10 ^ 70 +
        4405252563387595225879375568333502183629957064236549100788037970406482) * 10 ^ 70 +
        4807970598343463767495323443498557691383512468034674955009522038057603) * 10 ^ 70 +
        8193770626183176430143664665215546418588446435468641582631987713585996) * 10 ^ 70 +
        2243157672568067539249618740536212800902223396119234809575153123879997) * 10 ^ 70 +
        2800006587151820685218805700830132704255603858190506438032553685046460) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 0 +
    176 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 26 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (176 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_176 :
    recurrence5Scalar1First.coeff 176 =
      -((((((1141071 * 10 ^ 70 +
        9963879016043586952297679054487825057452021547135592844256805773873960) * 10 ^ 70 +
        5832412705092035735184218799709688326231142882611960423727524227548631) * 10 ^ 70 +
        7699985542605021673389082861635931440573965541171971314935609451115034) * 10 ^ 70 +
        9022502008654273461571885028221095593114566897777813787335063819543216) * 10 ^ 70 +
        7809909956955450272776390360452296649559410020781548554859664793460935) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 0 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 26 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (177 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_177 :
    recurrence5Scalar1First.coeff 177 =
      ((((((1987572 * 10 ^ 70 +
        0079069250075935838566743558660153485895605466244011510780727291085377) * 10 ^ 70 +
        1099785981834094751602274420087570593677556787611922625825919489666288) * 10 ^ 70 +
        1733709634448640216806558112314854738219067446784061810269151915508685) * 10 ^ 70 +
        5784066096170047786502402537260719392269903053388411897756368947068421) * 10 ^ 70 +
        6067330471255648841824098538635417038213532203665476844216451088878747) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 0 +
    178 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 26 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (178 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_178 :
    recurrence5Scalar1First.coeff 178 =
      -((((((3401507 * 10 ^ 70 +
        1891410460175264069962472774757350575020054096897533063063397533511055) * 10 ^ 70 +
        2814320875834070836729963039503426345916485500244130609780315745801744) * 10 ^ 70 +
        5152648645544270249190518354126405590358749901362772652829821062393348) * 10 ^ 70 +
        1571541965518107188901413117610456093632385951494349867766136715878571) * 10 ^ 70 +
        0072078585930097268643494008307884055282621582553610522667315994656438) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 0 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (179 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_179 :
    recurrence5Scalar1First.coeff 179 =
      ((((((5719593 * 10 ^ 70 +
        8403575633258796093609858493062349573905125995479759920322366730422632) * 10 ^ 70 +
        4326315112894192784069075654841337338551411597274859808266110189409567) * 10 ^ 70 +
        9836848924220602484929611929351616489865585230438691160431264092976931) * 10 ^ 70 +
        9527785323224026784370836633689575266871413128191067129265461220011958) * 10 ^ 70 +
        4689000237405439572631818086634619464779223004396939963545325902393886) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 0 +
    180 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 26 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (180 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_180 :
    recurrence5Scalar1First.coeff 180 =
      -((((((9449510 * 10 ^ 70 +
        0900172527489708026004815896041357311088760583710955073949206016364913) * 10 ^ 70 +
        5519239152541578843538284521718270454938594009327262645572019378302144) * 10 ^ 70 +
        4322860413917477986914342635929457706165269751700044192737410657318643) * 10 ^ 70 +
        6450621740364605399764236946619020148511059124324320852169666501849381) * 10 ^ 70 +
        6863224410151704775537796628033350696417813425392973731720621180579239) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 0 +
    181 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 26 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (181 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_181 :
    recurrence5Scalar1First.coeff 181 =
      ((((((15339354 * 10 ^ 70 +
        8629859065297105430047867654055718984473561494131507418683020641146346) * 10 ^ 70 +
        3885474799670841933740252908345828167691965451997345729564348975937189) * 10 ^ 70 +
        4886223243474051803405561237665300829237303074824526006959949712764272) * 10 ^ 70 +
        4823741848913583901225279006935853142852613260262463518866426601765542) * 10 ^ 70 +
        8347583796630659968060200704746900913042050292397802793316643529550781) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 0 +
    182 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 26 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (182 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_182 :
    recurrence5Scalar1First.coeff 182 =
      -((((((24465846 * 10 ^ 70 +
        0143661166661881462742739735470623645902945018991184151100915646243973) * 10 ^ 70 +
        0877466286204010268880912250651544869812946088508905075364570516891803) * 10 ^ 70 +
        6909152159564291756874560294663333289891791881967279809521969103741305) * 10 ^ 70 +
        2218186279521929619598687409954039280415518029070811593850519524811062) * 10 ^ 70 +
        3154151117121354147644364151668897910233449317871130186164112372090824) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 0 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 26 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (183 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_183 :
    recurrence5Scalar1First.coeff 183 =
      ((((((38341446 * 10 ^ 70 +
        6684298410637106504433657955684219505631897031048355318613076616479001) * 10 ^ 70 +
        7958548951768093275784194289044851249953213137975371910193161519680890) * 10 ^ 70 +
        9975612970108164720316813766387838097105982424346682522417378287548930) * 10 ^ 70 +
        6223675477703434376423840759417626005916026871725570348372775277695225) * 10 ^ 70 +
        9734476175008915156820825826397644620502588794302528037468866595831340) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 0 +
    184 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 26 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (184 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_184 :
    recurrence5Scalar1First.coeff 184 =
      -((((((59037726 * 10 ^ 70 +
        3929354769679135000495903266971851780319752308590869311434851404162077) * 10 ^ 70 +
        1032807139580163768793647006077127102011999674748756394927554261913783) * 10 ^ 70 +
        2810285267242336171043776837934432345837752658051214436730605102426063) * 10 ^ 70 +
        0202123608255487985933189278201123091750720691622902904588366662655479) * 10 ^ 70 +
        9132696573637205233243289354498495864730488240184955870480785332152605) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 0 +
    185 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 26 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (185 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_185 :
    recurrence5Scalar1First.coeff 185 =
      ((((((89318043 * 10 ^ 70 +
        6485639699531540085868660467770835226631880078228231164469298822545867) * 10 ^ 70 +
        7820024745341771758597440633631391378903883234714251157879642544694675) * 10 ^ 70 +
        1206906833692437942286900062916445812925281540292534564096071499850626) * 10 ^ 70 +
        3660961694696466333016619034664579204898111657117945074549593815185011) * 10 ^ 70 +
        0214619152893635902344184151175097873779662354478105134730263710886162) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 0 +
    186 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 26 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (186 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_186 :
    recurrence5Scalar1First.coeff 186 =
      -((((((132767090 * 10 ^ 70 +
        1736790310364512150864722450470506106561679799362506704831251355852444) * 10 ^ 70 +
        9177478177691808252240034730995321455288266616104781368196014154047098) * 10 ^ 70 +
        5170359853431304554880005245736673267424975847491329799560745900417583) * 10 ^ 70 +
        7406917030371623482641401220669113893731262308690708962086960423923667) * 10 ^ 70 +
        3399755277525837450711206717393190887043074398115032959222048533551765) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 0 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 26 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (187 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_187 :
    recurrence5Scalar1First.coeff 187 =
      ((((((193898274 * 10 ^ 70 +
        3488750761240401601336934392272897668034697482639256377397364323352730) * 10 ^ 70 +
        1080494513619063486195874546116985931881569429871111642148605720441172) * 10 ^ 70 +
        2460850699934371267711893048376730368726414873128172755028566799994499) * 10 ^ 70 +
        4960412908823321585263221965647300916586106839118755127289529296429311) * 10 ^ 70 +
        6892785634363702916106704256720438599469452118984264757053913613922782) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 0 +
    188 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 26 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (188 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_188 :
    recurrence5Scalar1First.coeff 188 =
      -((((((278213043 * 10 ^ 70 +
        3763893541498054538363193074134020831586601466652365791062750236181341) * 10 ^ 70 +
        9563633495613862795644943123984245322187773075825309339696879411982868) * 10 ^ 70 +
        4161203103924835652831366587678027008710782360278506617277627080942635) * 10 ^ 70 +
        2611348089323338976269954916425608223251014125346127925656008843238093) * 10 ^ 70 +
        4867617793508410036419771964867866850828538034915851217341137939338639) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 0 +
    189 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 26 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (189 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_189 :
    recurrence5Scalar1First.coeff 189 =
      ((((((392180211 * 10 ^ 70 +
        9012554066037258678361407920489217115613377045120160862491066391766666) * 10 ^ 70 +
        7940391593752655870576401644926199924099061506140289609225357943895057) * 10 ^ 70 +
        5055666928999757907436699254674361029199141988471964769981109217921271) * 10 ^ 70 +
        9349491528900430178813431573232077194707757977103542095610525409355606) * 10 ^ 70 +
        1645357373757450880697617554712345799255592068935491884471334284134125) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 0 +
    190 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 26 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1First_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (190 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_190 :
    recurrence5Scalar1First.coeff 190 =
      -((((((543099765 * 10 ^ 70 +
        4040147206785307909610482410880550403800342860727060242831941588802468) * 10 ^ 70 +
        3320257616546746972120026005410316354598831895458359322829953860018761) * 10 ^ 70 +
        9862946553613731865791944720347331829047413697575626445152095919996541) * 10 ^ 70 +
        3797714244817386937033052789748738175996109944437711702599664367277172) * 10 ^ 70 +
        1762703277554183004221968110231723238032390495649190117635552595917259) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 0 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 26 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
