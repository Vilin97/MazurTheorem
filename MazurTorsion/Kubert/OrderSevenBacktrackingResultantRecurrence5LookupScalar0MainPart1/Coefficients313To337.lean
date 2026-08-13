/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0MainPart1Simp
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

private theorem recurrence5Scalar0Main_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (313 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_313 :
    recurrence5Scalar0Main.coeff 313 =
      -(((((4811806701061781899662313539299400681881885333328625632683833 * 10 ^ 70 +
        6972815340581109519805237755986281794690750510395810880614932714490717) * 10 ^ 70 +
        8046175094241859152355120640413701946629854846262225364007030443102966) * 10 ^ 70 +
        4161547904408670526575469940311464249185537048564993483159220873604424) * 10 ^ 70 +
        3465709675562800112397715670784898071358498149779789042804407220260492) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 314 = 0 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 26 +
      160 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (314 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_314 :
    recurrence5Scalar0Main.coeff 314 =
      (((((2153437456443736930285733806939079909860687703395123590730612 * 10 ^ 70 +
        1589210559260373848242491045859897610290730270445547683420365536934471) * 10 ^ 70 +
        2669620167046337355341892022593267718375672866245144640521066474414900) * 10 ^ 70 +
        7533846760143487588825112893450769419321170361604876242019896194523797) * 10 ^ 70 +
        3368239405705056554602861129464259438486793997464121076656148267466180) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 315 = 1 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 25 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (315 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_315 :
    recurrence5Scalar0Main.coeff 315 =
      -(((((928582864853115210159674757155774421584676714410465498418913 * 10 ^ 70 +
        0564332297123049702515893863190817988263213512534207593254950670200259) * 10 ^ 70 +
        0365515843089006215074625442234593503680473114172058985913365633304518) * 10 ^ 70 +
        5707968434807116435612663520619645856878195078039177267399268184180148) * 10 ^ 70 +
        6031578091374684383281719027715197139311816865331020260504273517514856) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 316 = 2 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 24 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (316 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_316 :
    recurrence5Scalar0Main.coeff 316 =
      (((((384797867696057151076035612091858133195874323077600596344069 * 10 ^ 70 +
        7520025811849449612915273427221242187571822927221723528476018928074623) * 10 ^ 70 +
        7742996577489683987521833785058075409741315968218869906114950800747961) * 10 ^ 70 +
        3657933534456543227140447448078609325675657454628476253620057219802789) * 10 ^ 70 +
        5125310752430377929284212450251075582602433544974640781920194057189144) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 317 = 3 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 23 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (317 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_317 :
    recurrence5Scalar0Main.coeff 317 =
      -(((((152350468213636843511231182331566068113014119419452860836469 * 10 ^ 70 +
        5866147524110481322337694781264247553282800371847930821706669146871441) * 10 ^ 70 +
        0186041698851551862060070166722009830376518497379343684028323716221424) * 10 ^ 70 +
        0356459173502443091639666122841471300979062418317106679782314587840391) * 10 ^ 70 +
        9464022449405855794695211716855954083352498183767287008980784091912185) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 318 = 4 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 22 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (318 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_318 :
    recurrence5Scalar0Main.coeff 318 =
      (((((56977259457970865552892837852708793831729513110524423701342 * 10 ^ 70 +
        0591812891880041751534105551901418575141366197349252198096738466597667) * 10 ^ 70 +
        9281179256045394829088064124615261529230067038311301344225410812948426) * 10 ^ 70 +
        5169589834166679997453037305635954416838852906656170727202167111344453) * 10 ^ 70 +
        0661987448230725271917621519137943847229682031017250280377920435484750) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 319 = 5 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 21 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (319 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_319 :
    recurrence5Scalar0Main.coeff 319 =
      -(((((19668453122037812714546617447269658197878225824797970435907 * 10 ^ 70 +
        6639463451897055200077367170062776314421422590751334102321362320241698) * 10 ^ 70 +
        8489489239508177349078112039629593346188358912631810148511362403277422) * 10 ^ 70 +
        7225579693327186710941977093447290203927363869798756830399198869442347) * 10 ^ 70 +
        9603406601997393233598738511520028540540779810210537046090839581151787) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 320 = 6 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 20 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (320 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_320 :
    recurrence5Scalar0Main.coeff 320 =
      (((((5937006318297357578453869663502148560690131498262824720549 * 10 ^ 70 +
        2102409177750205524254228291557863697690062136453115268594154179184976) * 10 ^ 70 +
        1939600943867172313265032218408967274589053629570381796555523401183286) * 10 ^ 70 +
        4254583368726688845257416496670596078288951452284787965738133008794720) * 10 ^ 70 +
        1474011050192607889620533184827419141083646313364961929208254713347610) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 321 = 7 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 19 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (321 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_321 :
    recurrence5Scalar0Main.coeff 321 =
      -(((((1311352307905924916786306195773026528063988173936148581660 * 10 ^ 70 +
        1063973040237676458313022998459882304095286360546820103655083859749534) * 10 ^ 70 +
        1986349481471412925286404997328958094644750580840156691022311935632933) * 10 ^ 70 +
        1928878370901690122800158178610615964620198631318251876200566084857359) * 10 ^ 70 +
        0514489083921046411050883430741192457282901395321866406773759995897574) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 322 = 8 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 18 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (322 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_322 :
    recurrence5Scalar0Main.coeff 322 =
      -(((((21029889313775075506548710040655110081409655825394927163 * 10 ^ 70 +
        4994632559242933706296553599240330918273282589915138821967723146416806) * 10 ^ 70 +
        2598521321275669169273236162338820510314516860626779122035718023240315) * 10 ^ 70 +
        3721890242614846966716032168284236168390937687768527174657322014859347) * 10 ^ 70 +
        3988394167656769101294342017269131647947221459500616847714928818727905) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 323 = 9 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 17 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (323 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_323 :
    recurrence5Scalar0Main.coeff 323 =
      (((((274472756461046009456167087321017270610251930504173972227 * 10 ^ 70 +
        8858500905629877587990938714516856594377315253559677484761119676741898) * 10 ^ 70 +
        3127540028712140204660096017517127573670861076660284284983107994933749) * 10 ^ 70 +
        2259957272830779912564270894033055159184722908002646427612625257201457) * 10 ^ 70 +
        9036486762030961575313807938725613213047732320617443787700485538827706) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 324 = 10 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 16 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (324 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_324 :
    recurrence5Scalar0Main.coeff 324 =
      -(((((234551065821283221582252412606989007142550958840118790336 * 10 ^ 70 +
        4102317118348927073360334656817155709648935384038064789468713575176782) * 10 ^ 70 +
        5351348552451042803517780228031834741644126297114260140494319385205922) * 10 ^ 70 +
        5088274442305753591831931976317860811648546235280083104744116604890366) * 10 ^ 70 +
        9018903627354053817524193665346347827647310909664475845181075960261004) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 325 = 11 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 15 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (325 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_325 :
    recurrence5Scalar0Main.coeff 325 =
      (((((150486888119031806501531117923273634175101360389524805313 * 10 ^ 70 +
        4603864967058780765038771352807892629705172317064205488125742759124745) * 10 ^ 70 +
        4840710619246802413241629676434771892911328476415372752847818375470838) * 10 ^ 70 +
        0058327829637136159447356111909913191710093799240637863206326690292820) * 10 ^ 70 +
        1345932851859115638072507024584341603994280035823496315873106854306243) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 326 = 12 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 14 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (326 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_326 :
    recurrence5Scalar0Main.coeff 326 =
      -(((((85254880273976771391364856619000029849974890755106648015 * 10 ^ 70 +
        6813857503215766928746233816462228835712683750696462424740692917970925) * 10 ^ 70 +
        2584091336884760213561015077292356065811569454507666535239299145250273) * 10 ^ 70 +
        1921684646316812504965289422818447703725412129455712490416614932414624) * 10 ^ 70 +
        9782490600318311931994245649827448421918145741245558275600704946846331) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 327 = 13 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 13 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (327 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_327 :
    recurrence5Scalar0Main.coeff 327 =
      (((((44936867936440134751464998372148490709635246029414722733 * 10 ^ 70 +
        9576079497726444180519906757007149721691415855555654939417036289422275) * 10 ^ 70 +
        7494537228081768589138836681286785830627864468951983186806157078821834) * 10 ^ 70 +
        9950767934206852595318767260507140279905924459718555158831795657097370) * 10 ^ 70 +
        9377209450453055215711535123623199434543683492315101118591021360860037) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 328 = 14 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 12 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (328 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_328 :
    recurrence5Scalar0Main.coeff 328 =
      -(((((22569613063797856147225773421635581805311786883281022027 * 10 ^ 70 +
        0528711301127182834642304581680851083234526439080464880892204836854871) * 10 ^ 70 +
        5629923941867694901318216791344407464511141034578970327504375459299451) * 10 ^ 70 +
        2886732250996893984047595719151550989626930251807294154754709919476821) * 10 ^ 70 +
        1974869449554413024175981122254160733044907192148479863264591519044353) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 329 = 15 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 11 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (329 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_329 :
    recurrence5Scalar0Main.coeff 329 =
      (((((10943788571475073731680528780743448914171404571756963582 * 10 ^ 70 +
        8636197805159324378285277611813912760541195040905779955761557496384441) * 10 ^ 70 +
        5863715197521464045941490875124766669508297514273286855446947551022641) * 10 ^ 70 +
        6566530041691486506370045742999243484143817742290370369251759600046575) * 10 ^ 70 +
        5193406727438087940941339188189096152912937766777668644332441412442468) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 330 = 16 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 10 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (330 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_330 :
    recurrence5Scalar0Main.coeff 330 =
      -(((((5164086127416312815720030219587330540424699273514992035 * 10 ^ 70 +
        7847947880597813124128966724950397445952803207971562706979001269574324) * 10 ^ 70 +
        5276008116843209802910078125531224725073980302307902821076887917923762) * 10 ^ 70 +
        3137561972870933797941461257653161375852037889734701883636182904872883) * 10 ^ 70 +
        7147877039399639826296882814734883740404356987962968305921946010386666) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 331 = 17 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 9 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (331 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_331 :
    recurrence5Scalar0Main.coeff 331 =
      (((((2383524241346315948989825413288082228440776750219310036 * 10 ^ 70 +
        3970645345032149237276283514262174136475867038847422755140242659035284) * 10 ^ 70 +
        3089044596942851620184841951765760197726720047738821670550087582818302) * 10 ^ 70 +
        0115524435097170428606660994814376829743167470582436811713435691578621) * 10 ^ 70 +
        0438408004176761964812469367666371068779910098052354639046057623357109) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 18 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 8 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (332 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_332 :
    recurrence5Scalar0Main.coeff 332 =
      -(((((1079622631154934092998016436501371082841432582572070165 * 10 ^ 70 +
        3447166818616785541818843548042703305228272769558471576526978942473254) * 10 ^ 70 +
        0212226446332426989974833585632961154069767436709266671825860532351888) * 10 ^ 70 +
        6985752780514303755915388520864917073529283828985409032069176786224792) * 10 ^ 70 +
        0518310548432879559019665135361109319192553895872841068419592857810724) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 19 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 7 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (333 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_333 :
    recurrence5Scalar0Main.coeff 333 =
      (((((480859367652750027562602034827376265715357058646265933 * 10 ^ 70 +
        9324805478919996786204567842229959747344544567478693602864509610025416) * 10 ^ 70 +
        0549135054226914975664308565862078344288131547014391532721803701924441) * 10 ^ 70 +
        6708530350023714837813235459233375865115575730677222980776218359759639) * 10 ^ 70 +
        4488437158641365323110878432130611361497179183027569065240583829324281) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 20 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 6 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (334 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_334 :
    recurrence5Scalar0Main.coeff 334 =
      -(((((210818300234365191597517970764510321814051112135913949 * 10 ^ 70 +
        5953574171155671826028527155924456479581237436193787535469498650939054) * 10 ^ 70 +
        9700074516440042984485596734928896121934105863448530450848989154482579) * 10 ^ 70 +
        5275196733578758742331268906802575569233085798545503336083459861722426) * 10 ^ 70 +
        3959658799455164496935921550662924553761304272664864607393814711515922) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 21 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 5 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (335 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_335 :
    recurrence5Scalar0Main.coeff 335 =
      (((((91007756232421752604517083401853590969907117714799761 * 10 ^ 70 +
        5985946808770234461141716132133051211390954161416594077303595412839158) * 10 ^ 70 +
        1733674731586978786192039217899434191275590429267461424551848203743671) * 10 ^ 70 +
        4485725760297985707569922517872043870416592078839463824484295175060502) * 10 ^ 70 +
        2838060914124764977795267166798129584629116282792211949495346635082050) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 22 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 4 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (336 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_336 :
    recurrence5Scalar0Main.coeff 336 =
      -(((((38675269872823705631814210172705325432606102827228227 * 10 ^ 70 +
        9384410720944267067004934029977939174549733825627195713413650410222966) * 10 ^ 70 +
        1102952019984015186079402018547498656825249668918906982630379073030834) * 10 ^ 70 +
        2509091022402928297225270677933652225668621658238065134592596997122914) * 10 ^ 70 +
        8592296437579538546684744588913866267242713880660224228865781374984761) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 23 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 3 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient0.coeff x * recurrence5QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5QuotientConstant_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Main_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (337 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_337 :
    recurrence5Scalar0Main.coeff 337 =
      (((((16170344529088840707035991471588711450694595702331299 * 10 ^ 70 +
        3785280277420442086426880735070635677812772771725079558627307369840421) * 10 ^ 70 +
        4387988711183503780324773629052692177348249195924275162695212491284915) * 10 ^ 70 +
        7715019526665964652101984207327869033386572085966681087516011066053806) * 10 ^ 70 +
        6722027435464634422246645457515553005999925168803365945187896781303665) : ℚ) := by
  unfold recurrence5Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 24 +
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
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 2 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Main_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Main_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
