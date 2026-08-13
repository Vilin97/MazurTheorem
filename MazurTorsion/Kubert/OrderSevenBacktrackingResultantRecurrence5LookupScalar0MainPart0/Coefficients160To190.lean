/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0MainPart0Simp
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

private theorem recurrence5Scalar0Main_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (160 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_160 :
    recurrence5Scalar0Main.coeff 160 =
      -((((((27 * 10 ^ 70 +
        9256435911324353071291301928539825209647028183732403037184499549444031) * 10 ^ 70 +
        0591832502921189438980077767940063996028345095206299119147343319779936) * 10 ^ 70 +
        7140319581742389218388106203960750301225553901112726747975297586603052) * 10 ^ 70 +
        4866337115997685101610316720223284671811637051216615815559593683429564) * 10 ^ 70 +
        6541368208001107552056387915159881006511720122359000282321751135970133) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (161 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_161 :
    recurrence5Scalar0Main.coeff 161 =
      ((((((65 * 10 ^ 70 +
        8490817656237927186792929420372644488671557867384626239491728025729146) * 10 ^ 70 +
        1544344870967188433886718739419059741255399807846271387652036819255350) * 10 ^ 70 +
        7364805817854284626897687912983810173319514550756961567817851554919079) * 10 ^ 70 +
        0162222816010982698603268501042205056770800081936513860249542978634623) * 10 ^ 70 +
        3840268066807237951444692024503731039611389151966355408414937040867589) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (162 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_162 :
    recurrence5Scalar0Main.coeff 162 =
      -((((((152 * 10 ^ 70 +
        4770207181429895544168545197895091977361085663764814303334119222786275) * 10 ^ 70 +
        6036662617737822755724649656808122541328790745739183354516008881971961) * 10 ^ 70 +
        0399681331399877364772724288950180051128553723324022857590786934523319) * 10 ^ 70 +
        8071072196100357657085722657779906953313332294483827843222453837869470) * 10 ^ 70 +
        2417172606064228242539431495355763762239824900755615980663977039752769) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (163 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_163 :
    recurrence5Scalar0Main.coeff 163 =
      ((((((346 * 10 ^ 70 +
        7354136199671636150147310209686920018624343933536137944352913563579370) * 10 ^ 70 +
        9876158818533488657287565250117671972402530134947736817537883821338094) * 10 ^ 70 +
        7725591265091121640647402042903476028620121151341795473135650446562448) * 10 ^ 70 +
        3670433889736585234553304494850764497909495210529347647449167592440350) * 10 ^ 70 +
        0545558947367008038085532369362491411805976399373287162444431443281767) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (164 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_164 :
    recurrence5Scalar0Main.coeff 164 =
      -((((((774 * 10 ^ 70 +
        3928952885221816564709675305796265191945545353094441977845138264878789) * 10 ^ 70 +
        3872020915304169187847625492439606254835728939156477408512419339918591) * 10 ^ 70 +
        6813265136931973159375539127184849181158250030788049800308471810769169) * 10 ^ 70 +
        6170962160596382936395480601816281193793524002728559693552089661109117) * 10 ^ 70 +
        5527385385741648301821080827389955864167899278103575138092538408422614) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (165 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_165 :
    recurrence5Scalar0Main.coeff 165 =
      ((((((1698 * 10 ^ 70 +
        7261368150763537141479818678753949231307010353553219521228170365370732) * 10 ^ 70 +
        9065443566487916355779196559167103926972864559558042473415480923507239) * 10 ^ 70 +
        9111961162765749362622664982144330183502024169420351332840470237252234) * 10 ^ 70 +
        7449713032009155181722673470661171121304067270072523766547481546418232) * 10 ^ 70 +
        2506115056535583477086541006888885188770079785523458767452775679051003) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (166 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_166 :
    recurrence5Scalar0Main.coeff 166 =
      -((((((3660 * 10 ^ 70 +
        2690284089908474027820939439414551999730380863104331650114334528187116) * 10 ^ 70 +
        2160029654675149929890295819041857215919739066076221234826891791752411) * 10 ^ 70 +
        7270966041898162882692302952328638799429385859233579815266120848686870) * 10 ^ 70 +
        5541278392022769364931687865677600777462485607667825934879254751701479) * 10 ^ 70 +
        0730488573698655141900890007666005769905162893230754151277333656958503) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (167 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_167 :
    recurrence5Scalar0Main.coeff 167 =
      ((((((7747 * 10 ^ 70 +
        4425093265701723738176880476264299776063538041381540263681830797750761) * 10 ^ 70 +
        2524365536124338366705536216366862053915411238987414409661533690160915) * 10 ^ 70 +
        7772088082641753766469716797442900634305547884295100553614777042599635) * 10 ^ 70 +
        6443239736271812569675182788008227053206093107375999550559982679181151) * 10 ^ 70 +
        9795493024409582036197824748798184534498479551065774608560658260445062) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (168 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_168 :
    recurrence5Scalar0Main.coeff 168 =
      -((((((16109 * 10 ^ 70 +
        6777317493121103767276182017940499238649560575369241494444801062862543) * 10 ^ 70 +
        0401481616719935841314823739599531435347455225950463543208449034536300) * 10 ^ 70 +
        7414194569324465927200397816273654558397320558682621221837846647501190) * 10 ^ 70 +
        9498230683013339357777781979044762916642673131378777333031970125215797) * 10 ^ 70 +
        0633722600436141639456021689163958347645195034159279020776734047042211) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (169 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_169 :
    recurrence5Scalar0Main.coeff 169 =
      ((((((32909 * 10 ^ 70 +
        8003780689381898251435128797710030670410762461199660669969719052772820) * 10 ^ 70 +
        9818848356514099005023975930749189542409956603761276848754023715693224) * 10 ^ 70 +
        4967374081330692471185696292344197650520600685307222533698455090933773) * 10 ^ 70 +
        5747486336751911817745982334486848938774759730190766334556334304747389) * 10 ^ 70 +
        6039130843133389205977460378406201515915488402855418373207074695757721) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (170 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_170 :
    recurrence5Scalar0Main.coeff 170 =
      -((((((66054 * 10 ^ 70 +
        0864775807390685318180736088096274717554580218048772579172626920774978) * 10 ^ 70 +
        5094676413724226923024953565769682417234843316684411106061273464077983) * 10 ^ 70 +
        2746646998525914099548967810227193249034493551858429025397132572668569) * 10 ^ 70 +
        5336162365705026474118258608190798587654272031190647566744779567368145) * 10 ^ 70 +
        0763063851493460880108691087903623904337132563619651269273629217442453) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (171 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_171 :
    recurrence5Scalar0Main.coeff 171 =
      ((((((130267 * 10 ^ 70 +
        3913966256539621043437875800496066957548915769502625774804978390483892) * 10 ^ 70 +
        2234489698838736458822733880126961765267266935137574944130998113326716) * 10 ^ 70 +
        2481016465368143872051851017560765885810053011622821877954324732851620) * 10 ^ 70 +
        6457782378186851465499363102184723888927972604445198578859892731348683) * 10 ^ 70 +
        0330909873903318339748042876964175799463454972321976560241431644627139) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (172 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_172 :
    recurrence5Scalar0Main.coeff 172 =
      -((((((252440 * 10 ^ 70 +
        0603940738145149443243754043870910185623804940577351209040268705434706) * 10 ^ 70 +
        3277741411587011767663107184622322147361064756044762596187201381566368) * 10 ^ 70 +
        8747022084191344890000488502375261067070526619188158172535659956689368) * 10 ^ 70 +
        4411258311420139411760869822904553718245374253563558704660294748836715) * 10 ^ 70 +
        9765980561177213392685705121460959000705045217586770876294104579831560) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (173 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_173 :
    recurrence5Scalar0Main.coeff 173 =
      ((((((480719 * 10 ^ 70 +
        5142577169503436934773781524434661675859478305328979547493228391079047) * 10 ^ 70 +
        7047433996929225743281154111503660616742161193700422159943204024137869) * 10 ^ 70 +
        7607124057020192143072759129023065706299491028623954990005094221555077) * 10 ^ 70 +
        7227969962241540061043631984312178254356261658155995774415455423759348) * 10 ^ 70 +
        2553296773234705846789830847356398192695122581645356459781262570289512) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (174 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_174 :
    recurrence5Scalar0Main.coeff 174 =
      -((((((899621 * 10 ^ 70 +
        8328173875776864502580981623873370740160631488353606120352832570244465) * 10 ^ 70 +
        2423683438230815749456045385761691804436577137582040137273384843429708) * 10 ^ 70 +
        3429837375910932786639445168373895926219809079805857354762598912883346) * 10 ^ 70 +
        1010980567824258478543671570373925490572143468987027589972009294760777) * 10 ^ 70 +
        2276382217725118440039809378160668507013629932332261348534015374477641) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (175 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_175 :
    recurrence5Scalar0Main.coeff 175 =
      ((((((1654574 * 10 ^ 70 +
        3772670136735559528038363260596371532190639510136680384741489986044222) * 10 ^ 70 +
        6712379149950326375201536363846563384845753706028262792430834011107196) * 10 ^ 70 +
        5129466849496170098771578488027760616926060993897602514944006230485020) * 10 ^ 70 +
        9912420708948892571795303530852802785912722433279998611028384721418219) * 10 ^ 70 +
        5476893132656920371353884757578296508821512140551318142941965489054922) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (176 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_176 :
    recurrence5Scalar0Main.coeff 176 =
      -((((((2990842 * 10 ^ 70 +
        1114477919727829420971290417682013710576363648683563992599600771217339) * 10 ^ 70 +
        1311232830811056999411771352297126478828667777953335241706789473597083) * 10 ^ 70 +
        3351906211484409159382941927092249675993308559003944302009210381549526) * 10 ^ 70 +
        5124338232012783694572477291396783556783412505687842188742619771871207) * 10 ^ 70 +
        2179568038041397144149614877691762407378860992482018292946702502132538) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (177 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_177 :
    recurrence5Scalar0Main.coeff 177 =
      ((((((5313783 * 10 ^ 70 +
        9313247921054226750534017391636810636801792396297082428123267939646790) * 10 ^ 70 +
        4888172967344919413304801579849511375377468914967034365155170010525737) * 10 ^ 70 +
        4234336007831389804770771066771265412940708089942206071397301031850465) * 10 ^ 70 +
        0554378617611726959336577169543872999967872350294923694180229682191841) * 10 ^ 70 +
        3083139346252244839814160381599405406483543066209245858564831904954097) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (178 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_178 :
    recurrence5Scalar0Main.coeff 178 =
      -((((((9279816 * 10 ^ 70 +
        1210117371154704311406919244507088146481258953297823718512654651952350) * 10 ^ 70 +
        4358326132395284608290052605906340379162792512938372363523737191741232) * 10 ^ 70 +
        1061614591791414058054300260094263003093568781957693552403274131083065) * 10 ^ 70 +
        2625531152876176416697326683029192610479444531001791385964746663627113) * 10 ^ 70 +
        1552933663366731171246044052908652823006463378615796458194989870667115) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (179 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_179 :
    recurrence5Scalar0Main.coeff 179 =
      ((((((15930204 * 10 ^ 70 +
        3000069577704491195638075685411818235617995568025694267625526511667640) * 10 ^ 70 +
        1480079168567054423636234052251116534829237890778258059671091203150139) * 10 ^ 70 +
        8484253910925118818791968237490043865105119744560733114773445638881523) * 10 ^ 70 +
        3940522358652749469906527300386426332028664030332828196775783548003449) * 10 ^ 70 +
        0956200683314767719681006756291699992865174764069971230637494524248783) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (180 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_180 :
    recurrence5Scalar0Main.coeff 180 =
      -((((((26882571 * 10 ^ 70 +
        6218863391050655589305982500437282966222335788155391536115036106199319) * 10 ^ 70 +
        3834319382695107646155813913722164382082784103487054656952583729583845) * 10 ^ 70 +
        1529436978161162537726350643855361563920793257895614197449190661512275) * 10 ^ 70 +
        4231724159906606735790748999365274673543888613461033787802918314211671) * 10 ^ 70 +
        4173360553558304648711059767272147033067282081907571004605657797210112) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (181 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_181 :
    recurrence5Scalar0Main.coeff 181 =
      ((((((44597278 * 10 ^ 70 +
        9191128750665671609594600361288277624648636141885818134533764390613992) * 10 ^ 70 +
        9726776892464061662054980319133611318495628877803477618818942553932431) * 10 ^ 70 +
        6697346038983528544500306367434738845153264240855624619468360860286050) * 10 ^ 70 +
        2879169186005902495498657707378880348211574183575431256895953066225064) * 10 ^ 70 +
        6335404515204745394161144403827497646427933961763922745493424078065262) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (182 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_182 :
    recurrence5Scalar0Main.coeff 182 =
      -((((((72736802 * 10 ^ 70 +
        1026893808564056393505349287954389562623833957826619728530679435584612) * 10 ^ 70 +
        9455540824117407717556096557119188957273026253569486237651496994228403) * 10 ^ 70 +
        5042690054319447331817496878402055523418405238456026626010073694947114) * 10 ^ 70 +
        4469100677551191214775017297226164323428456002053502815598277117026360) * 10 ^ 70 +
        8487493466687483915208919373615558004679736188474563674064719492944474) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (183 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_183 :
    recurrence5Scalar0Main.coeff 183 =
      ((((((116634808 * 10 ^ 70 +
        8332007829050746694556317221386424392601606730999201659509403436683455) * 10 ^ 70 +
        8547495759709833884480826536112838056706751606081983368853195341151532) * 10 ^ 70 +
        4174279786586712583783555172408668968246093848993270095630370044186510) * 10 ^ 70 +
        9389178382718845952616681559761124112405581412960513187454005294966476) * 10 ^ 70 +
        9117893206047345709447672985555394799418619585887134045448116106819449) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (184 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_184 :
    recurrence5Scalar0Main.coeff 184 =
      -((((((183886478 * 10 ^ 70 +
        8631513674498713386405722322867025574989473390925234531838097188992564) * 10 ^ 70 +
        2211557688972659918204188093548398189532367628372293986782652367806657) * 10 ^ 70 +
        3237885635438296100242630580259403267543392146002251807715847100857078) * 10 ^ 70 +
        1740293150110881550526453095471784570060487884346731840026104210831890) * 10 ^ 70 +
        9096140756645182159748212145052160785663051340947497222519493131454232) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (185 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_185 :
    recurrence5Scalar0Main.coeff 185 =
      ((((((285061274 * 10 ^ 70 +
        1798658407682352063706540230375258630198195979869413744975531374472370) * 10 ^ 70 +
        5128509008375643037265369961385959922153661795125479177991604964021567) * 10 ^ 70 +
        5512542163760076075719767642742956399686122674930506825455869980646863) * 10 ^ 70 +
        3787000065018043726409082159822297933485655899794248676621610329162872) * 10 ^ 70 +
        7847864519243492237784574100677099398141780336173360483548895587694671) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (186 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_186 :
    recurrence5Scalar0Main.coeff 186 =
      -((((((434522554 * 10 ^ 70 +
        9206460507254485652572058209685015399102806695113995547296870731664923) * 10 ^ 70 +
        4697022836649865894241830293648373922413915292643275133271479123644039) * 10 ^ 70 +
        5797355343620714460482460311206173338009730097064624907808973623319387) * 10 ^ 70 +
        1698765557043769089692479547872047774456939501758816440305992850295875) * 10 ^ 70 +
        6164491984518248431587463818111561606779250619092734596879904618280185) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (187 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_187 :
    recurrence5Scalar0Main.coeff 187 =
      ((((((651314402 * 10 ^ 70 +
        7113126651999240876360626746595816881839666147528348976931956807627082) * 10 ^ 70 +
        0649694351583103576486753807236611465220350283723191930291341938771991) * 10 ^ 70 +
        5683990271681692997862699134353867367906623160526286088438662099989052) * 10 ^ 70 +
        2900271934897147865776696553812846525115515063458270487154360223887374) * 10 ^ 70 +
        9234561680041995929070945594829330426911896292503747459571957240825511) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (188 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_188 :
    recurrence5Scalar0Main.coeff 188 =
      -((((((960045023 * 10 ^ 70 +
        2320393054855685170690568342610231279410675418157070584046378329071095) * 10 ^ 70 +
        0638819205504431504759397838973516944216029240535061465771411693951827) * 10 ^ 70 +
        4963297894821052969814014494842876430689172387098852959234987263785631) * 10 ^ 70 +
        7830622398407946452418249475248125161905882097203645031627758640566048) * 10 ^ 70 +
        4006628869693690726851831471189181772094613441165310140725690715956998) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (189 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_189 :
    recurrence5Scalar0Main.coeff 189 =
      ((((((1391659955 * 10 ^ 70 +
        5798457869299522346153945795551786539850045831907675473099260686553356) * 10 ^ 70 +
        8872718841244190594122800400330478581459808502950742315567959800763937) * 10 ^ 70 +
        9873239983462027085099209446039124402403524632085826623841508930216978) * 10 ^ 70 +
        2932901866585460021597582571459446692578597613305323086469816796054856) * 10 ^ 70 +
        0851787828880033993784872137819751679064427269933172786974595138654478) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Main_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5QuotientConstant.coeff (190 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Main_coeff_190 :
    recurrence5Scalar0Main.coeff 190 =
      -((((((1983960776 * 10 ^ 70 +
        9540785511416465078179514189601926899068097477413712400691870732818189) * 10 ^ 70 +
        3405807560708880145940086088227321927888850021527890771174012635835453) * 10 ^ 70 +
        1101896117788519390154839189510573078184748572929342332039027430838893) * 10 ^ 70 +
        5978409246570663595110267267079354894642956785646582827218172125358146) * 10 ^ 70 +
        5584387718160611644473561138773623263064657583622415054420225097850924) : ℚ) := by
  unfold recurrence5Scalar0Main
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
  rw [recurrence5Scalar0Main_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
