/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0MainPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Main coefficient convolution

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

attribute [local simp]
  recurrence5QuotientConstant_coeff_38
  recurrence5QuotientConstant_coeff_39
  recurrence5QuotientConstant_coeff_40
  recurrence5QuotientConstant_coeff_41
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

attribute [local simp]
  recurrence5QuotientConstant_coeff_102
  recurrence5QuotientConstant_coeff_103
  recurrence5QuotientConstant_coeff_104
  recurrence5QuotientConstant_coeff_105
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

attribute [local simp]
  recurrence5QuotientConstant_coeff_166
  recurrence5QuotientConstant_coeff_167
  recurrence5QuotientConstant_coeff_168
  recurrence5QuotientConstant_coeff_169
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

attribute [local simp]
  recurrence5QuotientConstant_coeff_230
  recurrence5QuotientConstant_coeff_231
  recurrence5QuotientConstant_coeff_232
  recurrence5QuotientConstant_coeff_233
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

attribute [local simp]
  recurrence5QuotientConstant_coeff_294
  recurrence5QuotientConstant_coeff_295
  recurrence5QuotientConstant_coeff_296
  recurrence5QuotientConstant_coeff_297
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

private theorem recurrence5Scalar0Main_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (364 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_364 :
    recurrence5Scalar0Main.coeff 364 =
      (((((7146962727707921861272116329089706666677 * 10 ^ 70 +
        5674481770291097356689484383319573621959357568893276086818884011675141) * 10 ^ 70 +
        7592008919944187740858831372177715788485326055325663494829024460953625) * 10 ^ 70 +
        7150990330381802117625038655658318293800234259752926606659129713410318) * 10 ^ 70 +
        5058691574665509889410267256641965996804448071051977631285720604706256) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 218 = 7 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (365 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_365 :
    recurrence5Scalar0Main.coeff 365 =
      -(((((2623227210370648518776016836441982555192 * 10 ^ 70 +
        8427682998399430926933350944524079124473100189569064350500260073316270) * 10 ^ 70 +
        0255207547219281832043507633136881531346668097885877074044883957505446) * 10 ^ 70 +
        8144246193912657440324261490595258709691891963158953141070104642346326) * 10 ^ 70 +
        4134184864715396623137293788868493709700854197416249991114594667921577) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 218 = 6 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (366 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_366 :
    recurrence5Scalar0Main.coeff 366 =
      (((((942940802097640824588296022276186037777 * 10 ^ 70 +
        9813448873106028194639129963688857965778540272636300223558369373811190) * 10 ^ 70 +
        9769854942143274325506027872918360925075265124402535821650554310274189) * 10 ^ 70 +
        9345349079668337075583859666331392816109063026542097951686324064230308) * 10 ^ 70 +
        1604418124907613400495961696233638267236586406601928649231818566209341) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 218 = 5 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (367 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_367 :
    recurrence5Scalar0Main.coeff 367 =
      -(((((332245373275882828910455485489707299352 * 10 ^ 70 +
        8264473105894075738939482634401807996715304777785288635910920762293203) * 10 ^ 70 +
        7572189720676336116743063741647984465374001144383788125272463272849412) * 10 ^ 70 +
        7670208560475012947499798793088577479287921835662206270816551463119148) * 10 ^ 70 +
        1662274794953837217714321128011684287535930911212511476223561907242657) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rhs
    rw [show 218 = 4 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (368 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_368 :
    recurrence5Scalar0Main.coeff 368 =
      (((((114764279843929015650833732212103062930 * 10 ^ 70 +
        7702681413886189291684167381163150172949291674574039928313422728697236) * 10 ^ 70 +
        0261651458309960622577760003862426424525417324295175647141765819120880) * 10 ^ 70 +
        9175480047563430639004428011867016197301494632504093125519082999808419) * 10 ^ 70 +
        8855616944527233182358466537481764162719822731326994737170463984013386) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 3 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (369 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_369 :
    recurrence5Scalar0Main.coeff 369 =
      -(((((38848948815364981371013855561560867677 * 10 ^ 70 +
        7884477997024173863285582379886220808334584982280998248323319496975179) * 10 ^ 70 +
        5961962640510462759371778186331495935457950984389221489207796881677794) * 10 ^ 70 +
        6247411808904497820535048501895464653117958054115298471739481547349917) * 10 ^ 70 +
        8594094212404809452743270148446596751624048945876932629383471517645466) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 2 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (370 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_370 :
    recurrence5Scalar0Main.coeff 370 =
      (((((12880282337589060428082414555392521714 * 10 ^ 70 +
        3733848828784335745041469494612623401228401861926662418962998367266302) * 10 ^ 70 +
        9998828475134733074425367328542810246781151038688874157697691488160490) * 10 ^ 70 +
        5831848173858712094065567099994539457378363483637183547267039177296275) * 10 ^ 70 +
        1960810007308809372775289760836172511284802360055520545114465115868743) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 1 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (371 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_371 :
    recurrence5Scalar0Main.coeff 371 =
      -(((((4179720295307195820341333329092103279 * 10 ^ 70 +
        5035287453777001843456433611758734602096906436475669448412205766497500) * 10 ^ 70 +
        1021706724701049605063844369967944282924436601786450858910102232999535) * 10 ^ 70 +
        9689261991525791551056825619357292514098744252822910536098201311446769) * 10 ^ 70 +
        4013946625336697390110968819089249811138869282487428136376220648381457) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (372 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_372 :
    recurrence5Scalar0Main.coeff 372 =
      (((((1326568029668631628914708280255312152 * 10 ^ 70 +
        6172508061529661803531455127698200434575815587923153176243534618455944) * 10 ^ 70 +
        5298675737168562414127341031538666795190648238075597896612479487054423) * 10 ^ 70 +
        0794368637724032966523192686955382794097197845630503858950786506978724) * 10 ^ 70 +
        7772452505530942816429793104797742905863636294503286764197574220935818) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 31 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (373 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_373 :
    recurrence5Scalar0Main.coeff 373 =
      -(((((411480143879523214272993041304987560 * 10 ^ 70 +
        3167458453669120330640932765420983799628718405055722585355045958828475) * 10 ^ 70 +
        6281074219128369660159191131297317591032530890513693665729516879592838) * 10 ^ 70 +
        5461324228768351598281165480643906251935695122983198235067656662578491) * 10 ^ 70 +
        4907928867915542661306358191400333799033511587146077473010723213647865) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 30 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (374 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_374 :
    recurrence5Scalar0Main.coeff 374 =
      (((((124642927944712374963857532190788475 * 10 ^ 70 +
        6588380848989715872764583701251831798242065850024615332265267099915148) * 10 ^ 70 +
        5867638848817907798214366082688580604908680330704138468517093238148921) * 10 ^ 70 +
        9210892897699196063172489983360025752494174732789231631418695312347403) * 10 ^ 70 +
        3433203562355743278513639354012556617899999980991433874543646218505218) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 29 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (375 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_375 :
    recurrence5Scalar0Main.coeff 375 =
      -(((((36839748153129565568938132749434003 * 10 ^ 70 +
        0774229000276526695889951880478396078499497662682519021640928389783760) * 10 ^ 70 +
        4281528248727273030413759098284103323018390134136722715278339333031470) * 10 ^ 70 +
        7050447852641349674175248070449085888307524581304102935890064881837014) * 10 ^ 70 +
        7606646689175143701194666049220988881183049925569757812557917564253631) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 28 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (376 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_376 :
    recurrence5Scalar0Main.coeff 376 =
      (((((10613806361813187693736929826066649 * 10 ^ 70 +
        2707416648643549177461558067667055014143309649163796157411780451428626) * 10 ^ 70 +
        5534858807465909002517827980552311558928735781767182501704422044457831) * 10 ^ 70 +
        1963072251777552942133670173274134435220818771878075539187669377399952) * 10 ^ 70 +
        7184051033678559059546168836392377262112196499837764497904915640779994) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 27 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (377 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_377 :
    recurrence5Scalar0Main.coeff 377 =
      -(((((2977317226242300327864037051435895 * 10 ^ 70 +
        6444344551360624392609287652406275117069190979061592850515458354354639) * 10 ^ 70 +
        3792601172959914999286724065823893920407179738682200398137517858417889) * 10 ^ 70 +
        4577106555516716399751820851582566036086444884686238637204356126708498) * 10 ^ 70 +
        0112299937285778146407133863697958683344036793534433095025714079955652) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 26 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (378 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_378 :
    recurrence5Scalar0Main.coeff 378 =
      (((((812026096738758273535431824200792 * 10 ^ 70 +
        9948170206014855438529835624066156971610446885160747312971751901992668) * 10 ^ 70 +
        9121668760307916575174801379939063558312968448011134857050255707230492) * 10 ^ 70 +
        2357090555920904158591443490864774376235623435215280313356276064513578) * 10 ^ 70 +
        5853149015456318162154148358218178665855814014197957345063156212610501) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 25 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (379 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_379 :
    recurrence5Scalar0Main.coeff 379 =
      -(((((214973562088816272115360285163399 * 10 ^ 70 +
        0932657483364217268634372384655104545183189115774833910730110029509076) * 10 ^ 70 +
        3105569121152420747456832052031316724108950371023722011152142473109022) * 10 ^ 70 +
        8702031114848101611188265808891056817777333157400767467491233096706883) * 10 ^ 70 +
        0456378951783990203041147120268909795661093633534904486762649816365964) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 24 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (380 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_380 :
    recurrence5Scalar0Main.coeff 380 =
      (((((55137424235682532992506501633856 * 10 ^ 70 +
        9480722263271310721025992382952517212981975114749480702151502041846117) * 10 ^ 70 +
        4088026042495298784022042225479907828234945878829150653645152434867528) * 10 ^ 70 +
        6516807840339811418289861839104043226899571264635817285041803233171823) * 10 ^ 70 +
        4736248367748953926860815958244858872691835911317217048504316584718365) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 23 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (381 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_381 :
    recurrence5Scalar0Main.coeff 381 =
      -(((((13673011224297711244294400855240 * 10 ^ 70 +
        5865236873672214531588740623114593653374989508688277988246651419091963) * 10 ^ 70 +
        4134817350563610201068875496483495194359021030192773347646750800981942) * 10 ^ 70 +
        4409729215864744843754614811935814197959016696604552580789874531694908) * 10 ^ 70 +
        5813104155633307973934043733933160587852474563389074117295734660378840) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 22 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_381_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (382 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_382 :
    recurrence5Scalar0Main.coeff 382 =
      (((((3271592590047326942517227805356 * 10 ^ 70 +
        4884217424255607609632846000680437155995939403784725440051148715356208) * 10 ^ 70 +
        8342962438824763971609107941378375052037780210853514000570709017625869) * 10 ^ 70 +
        5590034776177537222077165637164528348383284837437094490792885379322353) * 10 ^ 70 +
        5720225120821320367486043199749698050431880349327084825894375168185227) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 21 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_382_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (383 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (383 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_383 :
    recurrence5Scalar0Main.coeff 383 =
      -(((((754057295857586083273922327987 * 10 ^ 70 +
        2558806870934222495871284668919280746075119289651152090389513934503675) * 10 ^ 70 +
        8586175184819965684451250460103653089384112551904439441960615000954955) * 10 ^ 70 +
        5605509775136621492789571805325806494368674009219928246272960885670636) * 10 ^ 70 +
        0555022298839410176862693005678633026438528442844671440044377701576169) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 20 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_383_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (384 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (384 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_384 :
    recurrence5Scalar0Main.coeff 384 =
      (((((167289937038198780582979926980 * 10 ^ 70 +
        6478492485436929350172297934087493541549486739727706212994261046638438) * 10 ^ 70 +
        8924547283028582941135287929354815895930397446859782906041970925618277) * 10 ^ 70 +
        3368955943947671121410991207778060133351507580854908852564411030967832) * 10 ^ 70 +
        0710379626806775109937420184147574817100320429304748641789592979696067) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 19 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_384_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (385 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (385 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_385 :
    recurrence5Scalar0Main.coeff 385 =
      -(((((35764239849705524005096649250 * 10 ^ 70 +
        1054535093863385335228704095327973966697976653307728921292443439542256) * 10 ^ 70 +
        7112350477271331441325435431632105825653269369867868341650473219532857) * 10 ^ 70 +
        5200188499366184928274403763088318034639488866229934340239482943090146) * 10 ^ 70 +
        5352404266188604418256846025719980616308622405693616110108881118288297) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 18 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_385_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (386 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (386 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_386 :
    recurrence5Scalar0Main.coeff 386 =
      (((((7402344305072828995584062010 * 10 ^ 70 +
        4771912664115116163708668935209373183966345387396904831281531556494961) * 10 ^ 70 +
        1397947639288492356465342727015915871166206095772352584887090232958007) * 10 ^ 70 +
        7585514653792984811841910034163113718795931490743170169415027860688886) * 10 ^ 70 +
        3289287157730861632861285215896532296843834427786939021139441176095067) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 17 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_386_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (387 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 234,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (387 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_387 :
    recurrence5Scalar0Main.coeff 387 =
      -(((((1499152984519948466088175529 * 10 ^ 70 +
        9878561838237756157152796670123175432809096469443315712246791365827670) * 10 ^ 70 +
        0127133521590075600404369344257970562364179603234901371384665617490734) * 10 ^ 70 +
        2077797845433609270576675105966939454294815572918339546933243325781264) * 10 ^ 70 +
        0324798689992417220838608177669846060848730951282491604279356876956355) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 16 +
      234 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_387_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (388 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 235,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (388 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_388 :
    recurrence5Scalar0Main.coeff 388 =
      (((((302808491172372464514240385 * 10 ^ 70 +
        1802421090799160576643523892500199263818926855527141382063518807317695) * 10 ^ 70 +
        9482342409741156951619052359672821265240932258037748887732399727220728) * 10 ^ 70 +
        3438971239015000255950434535303349994577781567927104148611816279108952) * 10 ^ 70 +
        5463452187475609824188674796138971353528344824076823687052654811300091) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 15 +
      235 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_388_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (389 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 236,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (389 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_389 :
    recurrence5Scalar0Main.coeff 389 =
      -(((((62674700576660066642970278 * 10 ^ 70 +
        2909353090380673312565040611377219094377204443355513025700999183990327) * 10 ^ 70 +
        1134480090494043304525381385578328131636220897831171387060018451247738) * 10 ^ 70 +
        6449378362779971822137925412409806873308639005682955896181509472418334) * 10 ^ 70 +
        8397772631935942953301709984736585624708115589282434997368269392061503) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 14 +
      236 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_389_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (390 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 237,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (390 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_390 :
    recurrence5Scalar0Main.coeff 390 =
      (((((13649816359377534571037456 * 10 ^ 70 +
        9088537087886186632676095623003848439480192137667343229358177159147933) * 10 ^ 70 +
        5424410309381288405453080043180498133687090957522238729395296838755331) * 10 ^ 70 +
        3510352897309828641088539232595932955662137842559919712688637701382834) * 10 ^ 70 +
        0483497040662889093160834485714623600813165505895862270835120006076782) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 13 +
      237 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_390_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (391 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 238,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (391 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_391 :
    recurrence5Scalar0Main.coeff 391 =
      -(((((3159939386108625948815919 * 10 ^ 70 +
        7515151287449363284894383151719512874873906456609789652884797532593782) * 10 ^ 70 +
        5109438101505133978992132137723695438614072403196136005332824940543587) * 10 ^ 70 +
        2740220681611148453734027010588767764101194353883806961902004681891008) * 10 ^ 70 +
        8777532372730257456775377549213239529710873057447027972769080417433757) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 12 +
      238 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_391_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (392 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 239,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (392 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_392 :
    recurrence5Scalar0Main.coeff 392 =
      (((((766319224235183960115476 * 10 ^ 70 +
        2719764781070493828774694014858712456989567609105510874478302294036884) * 10 ^ 70 +
        8171705594741164560940329790313594106043006158157760774822630164149049) * 10 ^ 70 +
        7298396521078417415382268963178020972357258491999602344569383880545631) * 10 ^ 70 +
        4740779783422302813591856889846207978139297245376256922701785218773663) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 11 +
      239 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_392_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (393 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 240,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (393 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_393 :
    recurrence5Scalar0Main.coeff 393 =
      -(((((189001235557261530176071 * 10 ^ 70 +
        6785848366090202135117900137057024684455035143638155488282336692508992) * 10 ^ 70 +
        0728617378915301045649989939039888959275871576853184119843248652831942) * 10 ^ 70 +
        2989964832210599045361191418428948496843833446382183125665560822438989) * 10 ^ 70 +
        8853281281296585641348474558708554585443407459886400847963303127888012) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 10 +
      240 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_393_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (394 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 241,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (394 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_394 :
    recurrence5Scalar0Main.coeff 394 =
      (((((46090698967703818114807 * 10 ^ 70 +
        2801138556376002549636840834193149937182488666751515524680713126088268) * 10 ^ 70 +
        8159400847343748481531315383266923886086545453760652525522762036748978) * 10 ^ 70 +
        1370176974223084296748250054887952413684942335396961310528389007426179) * 10 ^ 70 +
        3263802138563418523057501269765957346160511749669440888722383308070009) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 9 +
      241 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_394_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (395 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 242,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (395 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_395 :
    recurrence5Scalar0Main.coeff 395 =
      -(((((10920473915592416082687 * 10 ^ 70 +
        3647199216302693302576452549620238664458484929375210390507691263068445) * 10 ^ 70 +
        7894992009314093621486987926733821986576227332929720962661025339630554) * 10 ^ 70 +
        6020102958675426232196994028726906100840412363765631871065875558549074) * 10 ^ 70 +
        1888317320373643558089878138539793408534631325758710599640352390679850) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 8 +
      242 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_395_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (396 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 243,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (396 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_396 :
    recurrence5Scalar0Main.coeff 396 =
      (((((2500107150456819600997 * 10 ^ 70 +
        8149976371440611203998532954631265238753905532272247211848059034341422) * 10 ^ 70 +
        1151202094794812177728559271083667624032432942255633850670808996847628) * 10 ^ 70 +
        1396832825388288968092612414747973930919346187527653377488764578255977) * 10 ^ 70 +
        1555802987630661570107897694020202544743015832070291668562789072784563) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 7 +
      243 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_396_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (397 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 244,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (397 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_397 :
    recurrence5Scalar0Main.coeff 397 =
      -(((((555311819374579146618 * 10 ^ 70 +
        3835303960165322592839942087080245607826642748310630282705135098402447) * 10 ^ 70 +
        9754574502551645765201572816397136639397808322533523928937320411484785) * 10 ^ 70 +
        6500497803695553130788917413200639635974132108394307184201944578912826) * 10 ^ 70 +
        2684062440563475767943484606597594243690588656650257049774456966166880) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 6 +
      244 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_397_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (398 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 245,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (398 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_398 :
    recurrence5Scalar0Main.coeff 398 =
      (((((120640162950606750132 * 10 ^ 70 +
        3097909175957900720716000856633735851111604181652343230749792520483926) * 10 ^ 70 +
        3987565843749062946861190888816117128166883076257157964662065152937553) * 10 ^ 70 +
        9897642685633600999076756445138766352873598325434061556821054637198637) * 10 ^ 70 +
        2669472400553511831933796075322970313436809468332104263343009039658103) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 250 = 5 +
      245 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_398_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (399 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 246,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (399 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_399 :
    recurrence5Scalar0Main.coeff 399 =
      -(((((25701625645714149100 * 10 ^ 70 +
        3880580380998636470549940127957252115548329657430810978518629400084291) * 10 ^ 70 +
        7805338961629077908445038105523675176820570932540276318787600928374036) * 10 ^ 70 +
        5731305653785907952447765697663252058312277406243479601437077018718216) * 10 ^ 70 +
        6368833437328097249505084250649171139923477867001804397500930964168771) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rhs
    rw [show 250 = 4 +
      246 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_399_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (400 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 247,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (400 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_400 :
    recurrence5Scalar0Main.coeff 400 =
      (((((5296879527006933665 * 10 ^ 70 +
        9885130827995060264086875486110631858855679932582017223979817343547939) * 10 ^ 70 +
        6805075386021644865080640455951941921150325507627416829940583402561143) * 10 ^ 70 +
        7719267227822943087740511999755766875139749106430154038760792544717266) * 10 ^ 70 +
        9116966441983438081907960721624846369093218571604741931872323879994377) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 3 +
      247 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_400_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (401 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 248,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (401 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_401 :
    recurrence5Scalar0Main.coeff 401 =
      -(((((1017332262402784585 * 10 ^ 70 +
        1710982409430354942375147193556409488877079346792596054481687610811476) * 10 ^ 70 +
        9637256415355022357760080881222110451343416031521204327873207992545455) * 10 ^ 70 +
        6476036749627992321196009093259912530023111663986174358453809286620504) * 10 ^ 70 +
        8724260780258409647353155831704640843994835203088709888350367945044542) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 2 +
      248 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_401_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (402 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 249,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (402 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_402 :
    recurrence5Scalar0Main.coeff 402 =
      (((((169524541197688461 * 10 ^ 70 +
        2836954851038039002768485893176686673579544844471307745359283264759146) * 10 ^ 70 +
        0291416108077576282896836033573760485360512118806416401087280070776742) * 10 ^ 70 +
        4615473818302557399728964317377136415899020569285592670983365141519108) * 10 ^ 70 +
        4092320700438912465114257518420872620221078938780530256514328679047575) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 250 = 1 +
      249 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_402_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (403 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 250,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (403 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_403 :
    recurrence5Scalar0Main.coeff 403 =
      -(((((20643876190427402 * 10 ^ 70 +
        2976498636051615735479975871887196759816418749923275532006610173934032) * 10 ^ 70 +
        9365206296838787058021706819979157220818140963630069191772061264101855) * 10 ^ 70 +
        1368149916529335581587838771239410203864960418694607399248309492439312) * 10 ^ 70 +
        4799637380455523690561051897069994655741376004547030737851371688607405) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 32 +
      250 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_403_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (404 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 251,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (404 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_404 :
    recurrence5Scalar0Main.coeff 404 =
      (((((374139836899938 * 10 ^ 70 +
        8184575585117403718251174824605200871957337596719462933148390927153833) * 10 ^ 70 +
        3787957114060857598281827027137296229778188994920511678599009682850493) * 10 ^ 70 +
        6551041991069660166771806611710285666082790637674646404509689800225183) * 10 ^ 70 +
        7753358038465561301080454885668682400426703828073707893296847018832264) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 31 +
      251 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_404_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (405 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 252,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (405 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_405 :
    recurrence5Scalar0Main.coeff 405 =
      (((((742486097889676 * 10 ^ 70 +
        7719330783048619436974702206383044916431002923403522971050493926920454) * 10 ^ 70 +
        2754049417933885462634996503465839437493204621802786235456628680905556) * 10 ^ 70 +
        7925122953770234125794916154996523944767454045798204515377321034730112) * 10 ^ 70 +
        0786705157185599538163161410426570268658437156438858982864204961519303) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 30 +
      252 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_405_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (406 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 253,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (406 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_406 :
    recurrence5Scalar0Main.coeff 406 =
      -(((((280836470138840 * 10 ^ 70 +
        6794975729544039585396882413202769529640724717403389292940676146492036) * 10 ^ 70 +
        7545392910124614840399800568113826146462960501628192635451107494066052) * 10 ^ 70 +
        2569930973677815826367007218393554135219803871160975977481850759902682) * 10 ^ 70 +
        4052798979356619480849001989537120807173757060059512479416067120216707) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 29 +
      253 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_406_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (407 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 254,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (407 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_407 :
    recurrence5Scalar0Main.coeff 407 =
      (((((68912979107681 * 10 ^ 70 +
        0871619481280341615131505787180395858090123770067716593381175206550248) * 10 ^ 70 +
        1360954948679185161457803829912593388040480798417290305928694616007148) * 10 ^ 70 +
        7640420584196034133500797497611385384712768665260510452039132883014152) * 10 ^ 70 +
        0501784376850554804059578148848032346261491762621223280843349179565431) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 28 +
      254 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (408 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 255,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (408 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_408 :
    recurrence5Scalar0Main.coeff 408 =
      -(((((13127087900858 * 10 ^ 70 +
        7964239204235184567373756144698973117759979633408814082064375441413889) * 10 ^ 70 +
        7471321432238241285901818214075292971795772184856395962691595337224940) * 10 ^ 70 +
        2156669918293472961709547986036493699669396986999481072140550209354455) * 10 ^ 70 +
        1181982484562921500364278292424517233780987126363196575904188603246354) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 27 +
      255 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (409 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 256,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (409 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_409 :
    recurrence5Scalar0Main.coeff 409 =
      (((((2007622379995 * 10 ^ 70 +
        3815575652915288394847991501154340080477235438532722578638671825683801) * 10 ^ 70 +
        7745816334450176213056115681379211275299738947481751725496303597840828) * 10 ^ 70 +
        7371317128395477763275445007461347785050355230010287045471807503163329) * 10 ^ 70 +
        6609476431755190028903428149972387316380265645505575512686253718354471) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 26 +
      256 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (410 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 257,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (410 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_410 :
    recurrence5Scalar0Main.coeff 410 =
      -(((((240763502040 * 10 ^ 70 +
        2914866868965240233572377503729213332398160877585942135000908330626806) * 10 ^ 70 +
        4700467336818905014073747072917072530687653260312884929992865795403112) * 10 ^ 70 +
        3176940838932640318576183244719434521266586795034855320617208254779699) * 10 ^ 70 +
        7917660794294471786900075893515473835496958659291939023848953904584482) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 25 +
      257 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (411 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 258,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (411 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_411 :
    recurrence5Scalar0Main.coeff 411 =
      (((((19894142804 * 10 ^ 70 +
        9362699332014876430469941173338235033881643286226833655081113855911472) * 10 ^ 70 +
        5699552164268971723702139750965048476729683919255849206818993459343835) * 10 ^ 70 +
        2100029964885351113707671243378868779095467794887121489421787148161959) * 10 ^ 70 +
        8970872721146798221983876484313632428401804023870816043688803139020381) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 24 +
      258 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (412 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 259,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (412 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_412 :
    recurrence5Scalar0Main.coeff 412 =
      -(((((292935991 * 10 ^ 70 +
        1156973556808095126341374961372044328867130485899583656996934424933000) * 10 ^ 70 +
        3770597487034849343669313741011232315541548474449047060100178734302400) * 10 ^ 70 +
        9870673842471820480992334276180538968494584304427530084775275123536784) * 10 ^ 70 +
        3034508257784821778290512847739468500367973330182073975569985738437023) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 23 +
      259 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (413 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 260,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (413 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_413 :
    recurrence5Scalar0Main.coeff 413 =
      -(((((284162870 * 10 ^ 70 +
        4604093229409557446516073600259888866023628205817229347626164122848463) * 10 ^ 70 +
        9426307833491395557361904632335615275849039009679215782858984804584112) * 10 ^ 70 +
        1716777376641117295210393810989253099401532682683986693426451311763004) * 10 ^ 70 +
        1613406866554863026505251237286823015082301410817417704078480244280952) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 22 +
      260 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (414 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 261,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (414 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_414 :
    recurrence5Scalar0Main.coeff 414 =
      (((((72194434 * 10 ^ 70 +
        4206615586423639917672237258977965145620927092032464922259950677906699) * 10 ^ 70 +
        7303012221490962432768567122632861821929658305181773227794914096136250) * 10 ^ 70 +
        1504939120931407666488854464172614754483461128327688585589649832330537) * 10 ^ 70 +
        1573959821565459003960686104703387740296611865761273159892902821578878) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 21 +
      261 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (415 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 262,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (415 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_415 :
    recurrence5Scalar0Main.coeff 415 =
      -(((((12349303 * 10 ^ 70 +
        0805464130608440363356542459634018096675249147268120303221811372166464) * 10 ^ 70 +
        3765869547239461925419530834363686328330255773414377825638855088654242) * 10 ^ 70 +
        6477266868474373769588234200844420706886062381013983373199881687551217) * 10 ^ 70 +
        9592043845875305068299789302579907489796135587987293633916835569197997) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 20 +
      262 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (416 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 263,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (416 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_416 :
    recurrence5Scalar0Main.coeff 416 =
      (((((1715474 * 10 ^ 70 +
        0569212200162762532799884558212144578166413955370957203707250946109232) * 10 ^ 70 +
        6417630792613638388192091425990132865035016333755875691821739671221571) * 10 ^ 70 +
        0437898472488611849289584928209813148171890479358821391378596001885177) * 10 ^ 70 +
        7566543667070888362283703619027849127089945515012151011295644866512378) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 19 +
      263 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (417 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 264,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (417 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_417 :
    recurrence5Scalar0Main.coeff 417 =
      -(((((191623 * 10 ^ 70 +
        8528849666220634846245550256261473071885683969460971201938161738392598) * 10 ^ 70 +
        5245025661512643821649114708020652990206505372451009921843183649021180) * 10 ^ 70 +
        8867938276372895267093632819306291045950091625635153638128083891072994) * 10 ^ 70 +
        8518837525063930141789752882390275643390583063789904560235807924489881) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 18 +
      264 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (418 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 265,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (418 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_418 :
    recurrence5Scalar0Main.coeff 418 =
      (((((14354 * 10 ^ 70 +
        1041931183374738437455929287889847018229248945103335030549523483601492) * 10 ^ 70 +
        3671179730222411035806664660744826759479303961371193362305154704242491) * 10 ^ 70 +
        7790293354014596235661200969584595230180149784105346912027347592399079) * 10 ^ 70 +
        9939822624654740796570156042854790957829198861765561837599133909826907) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 17 +
      265 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (419 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 266,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (419 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_419 :
    recurrence5Scalar0Main.coeff 419 =
      (((((22 * 10 ^ 70 +
        1580308792253018023983433983974060760140882189121604762655313527294832) * 10 ^ 70 +
        8292682888792993868254058584127109063976778863611618804680762560861732) * 10 ^ 70 +
        4874023166524416240545876962741790362857866411408738805124541845409905) * 10 ^ 70 +
        2701537027948319791781102751086711343359357881880328833947417019603265) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 16 +
      266 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (420 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 267,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (420 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_420 :
    recurrence5Scalar0Main.coeff 420 =
      -(((((213 * 10 ^ 70 +
        0957849459399531544047880449247225562194145548418490786580026976206330) * 10 ^ 70 +
        3797140615479878502908494138419220865637468793933081777941477578372737) * 10 ^ 70 +
        0259936438924759244779004916192216136310109193355541423461510144420563) * 10 ^ 70 +
        4772783850182740400567745120037492230854596997082152812054650275473513) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 15 +
      267 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (421 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 268,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (421 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_421 :
    recurrence5Scalar0Main.coeff 421 =
      (((((37 * 10 ^ 70 +
        1348531445816456734595017895239336943510846500364194956429545247438018) * 10 ^ 70 +
        5940834695510220195853906614797630875819921855756154587362258300909446) * 10 ^ 70 +
        2622083115657939451137245541406644514142276420156971941207519213614115) * 10 ^ 70 +
        3866912598652946040715155814877687207391185293798434955525445865503422) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 14 +
      268 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (422 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 269,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (422 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_422 :
    recurrence5Scalar0Main.coeff 422 =
      -(((((3 * 10 ^ 70 +
        4387750614173072496695495999827346809497644443406394976565971153811777) * 10 ^ 70 +
        6305620415683838170067433110690447832200768210124835112189608656203565) * 10 ^ 70 +
        7333242640472533917368859187733058747434243433750018945308579182939737) * 10 ^ 70 +
        9860230328208464589616782226325528824515442852724405634296712843251326) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 13 +
      269 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (423 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 270,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (423 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_423 :
    recurrence5Scalar0Main.coeff 423 =
      ((((1178907545003459933460828229733192025666557167131207746519089297321234 * 10 ^ 70 +
        1063661783885405728426126564257169064140590123742772185958161875759543) * 10 ^ 70 +
        6271460100193490439213868728735408557186322279538294968577489002562296) * 10 ^ 70 +
        6050267969911246229785018906817539084335808949826563568413463539815689) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 12 +
      270 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (424 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 271,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (424 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_424 :
    recurrence5Scalar0Main.coeff 424 =
      ((((145073768332093958737135373081402555646026547690150393927014665499061 * 10 ^ 70 +
        5740262499402209769740210557497852888612143357237776246549422794021710) * 10 ^ 70 +
        7629730321737013693806960383189854864456203941952367453147047937496338) * 10 ^ 70 +
        9717829302482856059018551250843714824187806116493896421652195845302509) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 11 +
      271 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (425 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 272,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (425 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_425 :
    recurrence5Scalar0Main.coeff 425 =
      -((((24399334884394609226008394464764168890870745800324188011941350248362 * 10 ^ 70 +
        4794759628667562363351750819501048537941077290572664955919088205387750) * 10 ^ 70 +
        7450890670956139856231366775526953417202589252962561288639200733396888) * 10 ^ 70 +
        5143127183272176979867045750946114653801503845987788452370945288056472) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 10 +
      272 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (426 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 273,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (426 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_426 :
    recurrence5Scalar0Main.coeff 426 =
      ((((1413251311749934080010744168724600519764918393045336261126460775788 * 10 ^ 70 +
        1115510247416741178472641239625346049427740196188298964522353260095180) * 10 ^ 70 +
        2737019698951811200263462022410791986300021879356060251389885040271911) * 10 ^ 70 +
        8072670275348680386545321705290942386710402807580575391644888919829769) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 9 +
      273 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (427 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 274,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (427 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_427 :
    recurrence5Scalar0Main.coeff 427 =
      ((((13043895314869956326299340222520273456235654544873697545294278072 * 10 ^ 70 +
        6091028833255895307280104154031183931962526615677761660824081925903120) * 10 ^ 70 +
        1928050901525392035764279245949449543684978071197407442109312010665988) * 10 ^ 70 +
        7522341468431040942742974533930089260524624562345974964511959129783624) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 8 +
      274 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (428 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 275,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (428 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_428 :
    recurrence5Scalar0Main.coeff 428 =
      -((((7100030297621151701298878198833823940374013485886570535449378737 * 10 ^ 70 +
        7404542569950107578837036544397629625229811340562778242325000368825778) * 10 ^ 70 +
        6015567979549285754754442132040093919771932669482513116241709624421226) * 10 ^ 70 +
        1871994767611712410972930401281874474274023286885051875676192524033667) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 7 +
      275 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (429 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 276,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (429 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_429 :
    recurrence5Scalar0Main.coeff 429 =
      ((((354859713190620957183639863703682086260869637762674249500481455 * 10 ^ 70 +
        4583543845526814640223695853376525542080905848014387503608566935540832) * 10 ^ 70 +
        3940825416988323701688130611580284151292456994586416748650553048272305) * 10 ^ 70 +
        9294309334952787435354653912419776803545045558569050568572785472485786) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 6 +
      276 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (430 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 277,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (430 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_430 :
    recurrence5Scalar0Main.coeff 430 =
      ((((4599224409608284838395756061932888394299605501299939500930205 * 10 ^ 70 +
        7009387067143409236213830403520985866098275085436787289383586725879582) * 10 ^ 70 +
        7696840176593766404774066934768265239347057521368870004311328230623186) * 10 ^ 70 +
        4638832782613692422820928868048083007029905818468978384961655314245153) : ℚ) := by
  unfold recurrence5Scalar0Main
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
    rw [show 282 = 5 +
      277 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (431 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 278,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (431 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_431 :
    recurrence5Scalar0Main.coeff 431 =
      -((((940736638966834073161746083217311299338435193437319004916016 * 10 ^ 70 +
        6622071472798788859650170677758636600828394033748412512784964278242274) * 10 ^ 70 +
        2684510455305645401153927939593683155020551467875751085702277279438051) * 10 ^ 70 +
        0695641706496132043254128702843729126958573399005012714852503720465564) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 432 = 118 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 4 +
      278 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (432 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 279,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (432 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_432 :
    recurrence5Scalar0Main.coeff 432 =
      ((((11148808951195943806840171742219979248380297860200967960782 * 10 ^ 70 +
        9729289594007753807953181802862839533135951813405024146411443376432768) * 10 ^ 70 +
        0746421604112012274788047486159240011591995815183968215551627819447537) * 10 ^ 70 +
        2839697616468821638797754863034743116772551014896334032835805578306325) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 433 = 119 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 3 +
      279 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (433 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 280,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (433 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_433 :
    recurrence5Scalar0Main.coeff 433 =
      ((((1138425479016568633224877366728305648192691518497086285746 * 10 ^ 70 +
        5205875974599793661831517986280284154431621495250514971417160791160773) * 10 ^ 70 +
        7703399331734148940196310875871895352999721274546329431522345870436895) * 10 ^ 70 +
        0853493450487400808721650117532756377362178054674174061926788291816138) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 434 = 120 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 2 +
      280 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_433_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (434 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 281,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (434 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_434 :
    recurrence5Scalar0Main.coeff 434 =
      -((((11262806645747517109642305174607713209337387366558460356 * 10 ^ 70 +
        4640333238429894640651250100186954407035220685529391716774886375870933) * 10 ^ 70 +
        3536236383114340311890734587982050901384476534382713186316378585120885) * 10 ^ 70 +
        4220110506803306965006863730987074289034977898746411602355265532262817) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 435 = 121 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 282 = 1 +
      281 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_434_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (435 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 282,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (435 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_435 :
    recurrence5Scalar0Main.coeff 435 =
      -((((883017438806098136631808898532201937552066929449162008 * 10 ^ 70 +
        9673214507231920904035217182379744567672378752579049068487562892678544) * 10 ^ 70 +
        0865145488130275832629315944002105869666277171902196251571587525305341) * 10 ^ 70 +
        8049901596659794233375338344276121075329024253444666794810990732386302) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 436 = 122 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 32 +
      282 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_435_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (436 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 283,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (436 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_436 :
    recurrence5Scalar0Main.coeff 436 =
      -((((8075373127588762267450879417269157969264830121021650 * 10 ^ 70 +
        6768545751561893274040476609527666306493489547584172268901734382471136) * 10 ^ 70 +
        5539343314339120927993119856015175043217698917530030565297575446602003) * 10 ^ 70 +
        6385507637223440664758869417814183899763395248886427698061862012940843) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 437 = 123 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 31 +
      283 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_436_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (437 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 284,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (437 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_437 :
    recurrence5Scalar0Main.coeff 437 =
      ((((82794124884485880086533830522991673130104832516015 * 10 ^ 70 +
        4640946374240937916095799483509476577901762500237169811909828692879603) * 10 ^ 70 +
        0450467348731209773797732752110523433588859373816115722204874057586916) * 10 ^ 70 +
        3077886210157081540118981893548958793273787252789569228385443970754768) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 438 = 124 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 30 +
      284 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_437_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (438 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 285,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (438 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_438 :
    recurrence5Scalar0Main.coeff 438 =
      ((((1944468525963706521916752046839544118506789634026 * 10 ^ 70 +
        2525675842407296586730794020388806293443597629661070686804398125639769) * 10 ^ 70 +
        8661301722721935380244217590707434951036379248071419907436176351336966) * 10 ^ 70 +
        3068267732262614126679434618845970654089640520701527301358661709977987) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 439 = 125 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 29 +
      285 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_438_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (439 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 286,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (439 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_439 :
    recurrence5Scalar0Main.coeff 439 =
      ((((11999365146887203171226172540664260404414737171 * 10 ^ 70 +
        0769727799852045132231716103707804932108677227101892628936291833776624) * 10 ^ 70 +
        4209582289014259015024105093371827383537211160184123741574693721247693) * 10 ^ 70 +
        9940660497016874466194701738889553680070808186319402855898877111913817) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 440 = 126 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 28 +
      286 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_439_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (440 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 287,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (440 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_440 :
    recurrence5Scalar0Main.coeff 440 =
      ((((2773432163290604209292909499642353186293720 * 10 ^ 70 +
        3980961069507364553886080920100023936087548182038317533327028781872511) * 10 ^ 70 +
        9884968539108979985839431582817408929399838395112346153266006507467329) * 10 ^ 70 +
        7068642855353981988680493503643896140689618971426326436100315235221289) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 441 = 127 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 27 +
      287 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_440_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (441 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 288,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (441 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_441 :
    recurrence5Scalar0Main.coeff 441 =
      -((((300415899893571845569888719008955793173453 * 10 ^ 70 +
        3761768365590322033931196592079747610352926452498213155145947616046037) * 10 ^ 70 +
        2377797415778944811802114679436983130969680196300293526249299049886263) * 10 ^ 70 +
        8864171711876059497013372533388540472444504134526363419521440204860501) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 442 = 128 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 26 +
      288 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_441_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (442 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 289,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (442 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_442 :
    recurrence5Scalar0Main.coeff 442 =
      -((((1213890716309796824742788973725397974849 * 10 ^ 70 +
        3052311716866295238903774338697998015371686712941346737425204159825295) * 10 ^ 70 +
        2987064089568644180006832112687534444766481463311139152095539953539010) * 10 ^ 70 +
        2281162980173815901798688095067641355020515716086549208892484551449929) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 443 = 129 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 25 +
      289 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_442_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (443 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 290,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (443 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_443 :
    recurrence5Scalar0Main.coeff 443 =
      ((((289171398590377639336526744886022038 * 10 ^ 70 +
        0929877536320171182779590769802609224840306568202004438134556009969351) * 10 ^ 70 +
        5766373375949627391066867980707629232385661558179096437874789591247923) * 10 ^ 70 +
        5058284521466889173618054194069351394595400099583601409171732079067873) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 444 = 130 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 24 +
      290 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (444 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 291,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (444 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_444 :
    recurrence5Scalar0Main.coeff 444 =
      ((((12149378890335342538746241752191409 * 10 ^ 70 +
        0609366494974117067306791815779347363506497627880055251677956736939269) * 10 ^ 70 +
        7820444018783245279929387477799002898507865057873303099917515736988287) * 10 ^ 70 +
        6145439074869697794848540243846172811275125910262960254494127906349987) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 445 = 131 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 23 +
      291 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (445 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 292,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (445 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_445 :
    recurrence5Scalar0Main.coeff 445 =
      ((((18493783809149720281937853847805 * 10 ^ 70 +
        4721029391604835151388929901796839163911610442601209956950643579173643) * 10 ^ 70 +
        7355208927295085859975648135276128939019125151547962197350153894315574) * 10 ^ 70 +
        7309548881419464289240311362728813689237440496610139067422185603730714) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 446 = 132 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 22 +
      292 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (446 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 293,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (446 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_446 :
    recurrence5Scalar0Main.coeff 446 =
      -((((42151848696149705338953622085 * 10 ^ 70 +
        2294960240341755598498279310499340843586808460805366136662464853625224) * 10 ^ 70 +
        5612585320819458387690873688285799683375324270219966715297593099671159) * 10 ^ 70 +
        4997648203020409367477727620622139569473847332224310395350474095698986) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 447 = 133 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 21 +
      293 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (447 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 294,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (447 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_447 :
    recurrence5Scalar0Main.coeff 447 =
      -((((116517235068877594931168001 * 10 ^ 70 +
        9928088316240261253479281891482150474804051947886183336622373919383788) * 10 ^ 70 +
        3685312468530373197736912282576226265701119865868004626344852377802043) * 10 ^ 70 +
        2937248297533674534463789105941302832117421117033262821307323107597911) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 448 = 134 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 20 +
      294 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (448 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 295,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (448 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_448 :
    recurrence5Scalar0Main.coeff 448 =
      ((((42896323840478683287989 * 10 ^ 70 +
        1087753087160695139350201536801540921747513222531720401038745787661175) * 10 ^ 70 +
        8240741730394844938825951821795982769753119161358573603804858570863251) * 10 ^ 70 +
        4448009656991763244160362862427897673127645538564156105258605154150802) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 449 = 135 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 19 +
      295 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (449 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 296,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (449 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_449 :
    recurrence5Scalar0Main.coeff 449 =
      ((((274359424840146133717 * 10 ^ 70 +
        4906441497581998168180130090291230072840092169131831966252028133510597) * 10 ^ 70 +
        2810951500168719090665668309787434565163240607121231728676200816276647) * 10 ^ 70 +
        0997836081592388770077258840560880843654083420378167571176916079681726) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 450 = 136 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 18 +
      296 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (450 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 297,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (450 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_450 :
    recurrence5Scalar0Main.coeff 450 =
      ((((45116449301245776 * 10 ^ 70 +
        9233175194914699952808802790167268795925510303566697235735214961140365) * 10 ^ 70 +
        1698659692021026228649445327387249627202668730693356355682729915249881) * 10 ^ 70 +
        4665180563039565043786898789368690903988348533687718361860893045615060) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 451 = 137 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 17 +
      297 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (451 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 298,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (451 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_451 :
    recurrence5Scalar0Main.coeff 451 =
      -((((239004295399553 * 10 ^ 70 +
        6721296995451914569921549007417055125852994824452384654569016270567749) * 10 ^ 70 +
        5999263219856072630208049424470090178019568478294808332685695498361740) * 10 ^ 70 +
        1481642049793805159967228315543516048840614307889955466037775220026643) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 452 = 138 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 16 +
      298 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (452 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 299,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (452 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_452 :
    recurrence5Scalar0Main.coeff 452 =
      -((((93282117368 * 10 ^ 70 +
        5500045693248618682786531031965015309192549045162092374791089439871460) * 10 ^ 70 +
        1209185037937221314537873498496067166854704416259510399476356828063081) * 10 ^ 70 +
        5757159548248826371004738995735287586844703194624009059233097718307567) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 453 = 139 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 15 +
      299 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (453 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 300,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (453 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_453 :
    recurrence5Scalar0Main.coeff 453 =
      ((((36747353 * 10 ^ 70 +
        8529889147006331232351281609919762586021005243459389729191272983637264) * 10 ^ 70 +
        2730036672478859248235362081784405950331467893033109198025483271172360) * 10 ^ 70 +
        7135042832512010472146752177080370973739867770936025609136724746396765) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 454 = 140 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 14 +
      300 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (454 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 301,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (454 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_454 :
    recurrence5Scalar0Main.coeff 454 =
      ((((13288 * 10 ^ 70 +
        3542672029243738175127409398330914805082632346195410035997725811223041) * 10 ^ 70 +
        2809452390312981363771344220017863583269912018768935593519269029918043) * 10 ^ 70 +
        3668676627106446190625904645093720843958247491961256974475973146126291) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 455 = 141 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 13 +
      301 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (455 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 302,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (455 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_455 :
    recurrence5Scalar0Main.coeff 455 =
      (((712869808536946186843332236193545923216551243282650669185388610376345 * 10 ^ 70 +
        2789599542386774085231174596984987583508625637726320837099970480472942) * 10 ^ 70 +
        1873078395726710904949786080728065136066697422521303794211203851858292) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 456 = 142 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 12 +
      302 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (456 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 303,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (456 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_456 :
    recurrence5Scalar0Main.coeff 456 =
      -(((1517197697623935036538035191608929836258198481837684494586023431010 * 10 ^ 70 +
        1044946176825201451417223113258262827845531490018257426811052661227032) * 10 ^ 70 +
        3999560661251408904677315181648441951433265135202118989619628527406066) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 457 = 143 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 11 +
      303 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_456_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (457 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 304,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (457 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_457 :
    recurrence5Scalar0Main.coeff 457 =
      -(((43661206920242643661579409369597076555324232929204373822081963 * 10 ^ 70 +
        2172198468042875932866186031456967955019601054209013030193701829730568) * 10 ^ 70 +
        2414327768709385961106271202058292180159105583383341642119021556458732) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 458 = 144 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 10 +
      304 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_457_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (458 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 305,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (458 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_458 :
    recurrence5Scalar0Main.coeff 458 =
      (((759698732783435221274580878656422518329583935758633804964 * 10 ^ 70 +
        1316006425073445208088946401856829915482226850291800497533801027612956) * 10 ^ 70 +
        8082499667839153273383842888472267774819093573612991242895286812080189) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 459 = 145 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 9 +
      305 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (459 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 306,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (459 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_459 :
    recurrence5Scalar0Main.coeff 459 =
      (((18949477199781319543991511200603329311045695711231455 * 10 ^ 70 +
        2662702652409957989252464128010223303406801116612490108367412354381871) * 10 ^ 70 +
        3130263644064175190587973914761614799570706441320032170003116269444038) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 460 = 146 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 8 +
      306 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (460 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 307,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (460 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_460 :
    recurrence5Scalar0Main.coeff 460 =
      (((15166976135906443106729322861001631247679980797 * 10 ^ 70 +
        8319920267905188536287156291034574563833658728793687469833855503813270) * 10 ^ 70 +
        4532030067809073017584800376294060768286797005903429109837195886663836) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 461 = 147 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 7 +
      307 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (461 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 308,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (461 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_461 :
    recurrence5Scalar0Main.coeff 461 =
      -(((197630824172507266325736324820677063265112 * 10 ^ 70 +
        8685245161855206195603235278763741624063632671334572775945979564043906) * 10 ^ 70 +
        2321745468170739449907456857578878429348033184346593909517614410064437) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 462 = 148 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 6 +
      308 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (462 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 309,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (462 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_462 :
    recurrence5Scalar0Main.coeff 462 =
      -(((181392456047938424509580808975210742 * 10 ^ 70 +
        0997599162735797558851389514377989049923235745343309566779925318007032) * 10 ^ 70 +
        8356320346899808259458217651451980260784296036617479772141780017888688) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 463 = 149 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 5 +
      309 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (463 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 310,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (463 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_463 :
    recurrence5Scalar0Main.coeff 463 =
      (((17338000134524070614664361959 * 10 ^ 70 +
        4400260652508017526574411088953251086959114263739567485295252130764856) * 10 ^ 70 +
        8597731073038719615353104946255625373976087227813307499222687038569037) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 464 = 150 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 4 +
      310 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_463_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (464 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 311,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (464 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_464 :
    recurrence5Scalar0Main.coeff 464 =
      (((8754284402841494843980 * 10 ^ 70 +
        0864758140698624645332804387193471799086593289980656413401074029365806) * 10 ^ 70 +
        3907361619093700190966619648271507305806769262876736345238698791203565) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 465 = 151 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 3 +
      311 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_464_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 152,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (465 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 312,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (465 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_465 :
    recurrence5Scalar0Main.coeff 465 =
      (((172370598196642 * 10 ^ 70 +
        3067554993867207813815607363470763706760572310256053544187593315356057) * 10 ^ 70 +
        4209632576650395749733933851212989629614278753372444568006544191247254) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 466 = 152 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 2 +
      312 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_465_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 153,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (466 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 313,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (466 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_466 :
    recurrence5Scalar0Main.coeff 466 =
      -(((972305 * 10 ^ 70 +
        9624297323255745999893397617986012094444790851185499710285758685708607) * 10 ^ 70 +
        8343589289567456874932801618798842961058961385627623145777970469268349) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 467 = 153 +
    314 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 314 = 1 +
      313 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_466_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
