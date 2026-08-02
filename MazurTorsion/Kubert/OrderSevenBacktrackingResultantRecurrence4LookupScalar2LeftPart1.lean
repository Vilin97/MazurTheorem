/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A2_coeff_0
  recurrence4A2_coeff_1
  recurrence4A2_coeff_10
  recurrence4A2_coeff_100
  recurrence4A2_coeff_101
  recurrence4A2_coeff_102
  recurrence4A2_coeff_103
  recurrence4A2_coeff_104
  recurrence4A2_coeff_105
  recurrence4A2_coeff_106
  recurrence4A2_coeff_107
  recurrence4A2_coeff_108
  recurrence4A2_coeff_109
  recurrence4A2_coeff_11
  recurrence4A2_coeff_110
  recurrence4A2_coeff_111
  recurrence4A2_coeff_112
  recurrence4A2_coeff_113
  recurrence4A2_coeff_114
  recurrence4A2_coeff_115
  recurrence4A2_coeff_116
  recurrence4A2_coeff_117
  recurrence4A2_coeff_118
  recurrence4A2_coeff_119
  recurrence4A2_coeff_12
  recurrence4A2_coeff_120
  recurrence4A2_coeff_121
  recurrence4A2_coeff_122
  recurrence4A2_coeff_123
  recurrence4A2_coeff_124
  recurrence4A2_coeff_125
  recurrence4A2_coeff_126
  recurrence4A2_coeff_127
  recurrence4A2_coeff_128
  recurrence4A2_coeff_129
  recurrence4A2_coeff_13
  recurrence4A2_coeff_130
  recurrence4A2_coeff_131
  recurrence4A2_coeff_132
  recurrence4A2_coeff_133
  recurrence4A2_coeff_134
  recurrence4A2_coeff_135
  recurrence4A2_coeff_136
  recurrence4A2_coeff_137
  recurrence4A2_coeff_138
  recurrence4A2_coeff_139
  recurrence4A2_coeff_14
  recurrence4A2_coeff_140
  recurrence4A2_coeff_141
  recurrence4A2_coeff_142
  recurrence4A2_coeff_143
  recurrence4A2_coeff_144
  recurrence4A2_coeff_145
  recurrence4A2_coeff_146
  recurrence4A2_coeff_147
  recurrence4A2_coeff_148
  recurrence4A2_coeff_149
  recurrence4A2_coeff_15
  recurrence4A2_coeff_150
  recurrence4A2_coeff_151
  recurrence4A2_coeff_152
  recurrence4A2_coeff_153
  recurrence4A2_coeff_154
  recurrence4A2_coeff_155

attribute [local simp]
  recurrence4A2_coeff_156
  recurrence4A2_coeff_157
  recurrence4A2_coeff_158
  recurrence4A2_coeff_159
  recurrence4A2_coeff_16
  recurrence4A2_coeff_160
  recurrence4A2_coeff_161
  recurrence4A2_coeff_162
  recurrence4A2_coeff_163
  recurrence4A2_coeff_164
  recurrence4A2_coeff_165
  recurrence4A2_coeff_166
  recurrence4A2_coeff_167
  recurrence4A2_coeff_168
  recurrence4A2_coeff_169
  recurrence4A2_coeff_17
  recurrence4A2_coeff_170
  recurrence4A2_coeff_171
  recurrence4A2_coeff_172
  recurrence4A2_coeff_173
  recurrence4A2_coeff_174
  recurrence4A2_coeff_175
  recurrence4A2_coeff_176
  recurrence4A2_coeff_177
  recurrence4A2_coeff_178
  recurrence4A2_coeff_179
  recurrence4A2_coeff_18
  recurrence4A2_coeff_180
  recurrence4A2_coeff_181
  recurrence4A2_coeff_182
  recurrence4A2_coeff_183
  recurrence4A2_coeff_184
  recurrence4A2_coeff_185
  recurrence4A2_coeff_186
  recurrence4A2_coeff_19
  recurrence4A2_coeff_2
  recurrence4A2_coeff_20
  recurrence4A2_coeff_21
  recurrence4A2_coeff_22
  recurrence4A2_coeff_23
  recurrence4A2_coeff_24
  recurrence4A2_coeff_25
  recurrence4A2_coeff_26
  recurrence4A2_coeff_27
  recurrence4A2_coeff_28
  recurrence4A2_coeff_29
  recurrence4A2_coeff_3
  recurrence4A2_coeff_30
  recurrence4A2_coeff_31
  recurrence4A2_coeff_32
  recurrence4A2_coeff_33
  recurrence4A2_coeff_34
  recurrence4A2_coeff_35
  recurrence4A2_coeff_36
  recurrence4A2_coeff_37
  recurrence4A2_coeff_38
  recurrence4A2_coeff_39
  recurrence4A2_coeff_4
  recurrence4A2_coeff_40
  recurrence4A2_coeff_41
  recurrence4A2_coeff_42
  recurrence4A2_coeff_43
  recurrence4A2_coeff_44
  recurrence4A2_coeff_45

attribute [local simp]
  recurrence4A2_coeff_46
  recurrence4A2_coeff_47
  recurrence4A2_coeff_48
  recurrence4A2_coeff_49
  recurrence4A2_coeff_5
  recurrence4A2_coeff_50
  recurrence4A2_coeff_51
  recurrence4A2_coeff_52
  recurrence4A2_coeff_53
  recurrence4A2_coeff_54
  recurrence4A2_coeff_55
  recurrence4A2_coeff_56
  recurrence4A2_coeff_57
  recurrence4A2_coeff_58
  recurrence4A2_coeff_59
  recurrence4A2_coeff_6
  recurrence4A2_coeff_60
  recurrence4A2_coeff_61
  recurrence4A2_coeff_62
  recurrence4A2_coeff_63
  recurrence4A2_coeff_64
  recurrence4A2_coeff_65
  recurrence4A2_coeff_66
  recurrence4A2_coeff_67
  recurrence4A2_coeff_68
  recurrence4A2_coeff_69
  recurrence4A2_coeff_7
  recurrence4A2_coeff_70
  recurrence4A2_coeff_71
  recurrence4A2_coeff_72
  recurrence4A2_coeff_73
  recurrence4A2_coeff_74
  recurrence4A2_coeff_75
  recurrence4A2_coeff_76
  recurrence4A2_coeff_77
  recurrence4A2_coeff_78
  recurrence4A2_coeff_79
  recurrence4A2_coeff_8
  recurrence4A2_coeff_80
  recurrence4A2_coeff_81
  recurrence4A2_coeff_82
  recurrence4A2_coeff_83
  recurrence4A2_coeff_84
  recurrence4A2_coeff_85
  recurrence4A2_coeff_86
  recurrence4A2_coeff_87
  recurrence4A2_coeff_88
  recurrence4A2_coeff_89
  recurrence4A2_coeff_9
  recurrence4A2_coeff_90
  recurrence4A2_coeff_91
  recurrence4A2_coeff_92
  recurrence4A2_coeff_93
  recurrence4A2_coeff_94
  recurrence4A2_coeff_95
  recurrence4A2_coeff_96
  recurrence4A2_coeff_97
  recurrence4A2_coeff_98
  recurrence4A2_coeff_99
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101
  recurrence4LeadingSquare_coeff_102
  recurrence4LeadingSquare_coeff_103
  recurrence4LeadingSquare_coeff_104

attribute [local simp]
  recurrence4LeadingSquare_coeff_105
  recurrence4LeadingSquare_coeff_106
  recurrence4LeadingSquare_coeff_107
  recurrence4LeadingSquare_coeff_108
  recurrence4LeadingSquare_coeff_109
  recurrence4LeadingSquare_coeff_110
  recurrence4LeadingSquare_coeff_111
  recurrence4LeadingSquare_coeff_112
  recurrence4LeadingSquare_coeff_113
  recurrence4LeadingSquare_coeff_114
  recurrence4LeadingSquare_coeff_115
  recurrence4LeadingSquare_coeff_116
  recurrence4LeadingSquare_coeff_117
  recurrence4LeadingSquare_coeff_118
  recurrence4LeadingSquare_coeff_119
  recurrence4LeadingSquare_coeff_120
  recurrence4LeadingSquare_coeff_121
  recurrence4LeadingSquare_coeff_122
  recurrence4LeadingSquare_coeff_123
  recurrence4LeadingSquare_coeff_124
  recurrence4LeadingSquare_coeff_125
  recurrence4LeadingSquare_coeff_126
  recurrence4LeadingSquare_coeff_127
  recurrence4LeadingSquare_coeff_128
  recurrence4LeadingSquare_coeff_129
  recurrence4LeadingSquare_coeff_130
  recurrence4LeadingSquare_coeff_131
  recurrence4LeadingSquare_coeff_132
  recurrence4LeadingSquare_coeff_133
  recurrence4LeadingSquare_coeff_134
  recurrence4LeadingSquare_coeff_135
  recurrence4LeadingSquare_coeff_136
  recurrence4LeadingSquare_coeff_137
  recurrence4LeadingSquare_coeff_138
  recurrence4LeadingSquare_coeff_139
  recurrence4LeadingSquare_coeff_140
  recurrence4LeadingSquare_coeff_141
  recurrence4LeadingSquare_coeff_142
  recurrence4LeadingSquare_coeff_143
  recurrence4LeadingSquare_coeff_144
  recurrence4LeadingSquare_coeff_145
  recurrence4LeadingSquare_coeff_146
  recurrence4LeadingSquare_coeff_147
  recurrence4LeadingSquare_coeff_148
  recurrence4LeadingSquare_coeff_149
  recurrence4LeadingSquare_coeff_150
  recurrence4LeadingSquare_coeff_151
  recurrence4LeadingSquare_coeff_152
  recurrence4LeadingSquare_coeff_153
  recurrence4LeadingSquare_coeff_154
  recurrence4LeadingSquare_coeff_155
  recurrence4LeadingSquare_coeff_156
  recurrence4LeadingSquare_coeff_157
  recurrence4LeadingSquare_coeff_158
  recurrence4LeadingSquare_coeff_159
  recurrence4LeadingSquare_coeff_160
  recurrence4LeadingSquare_coeff_161
  recurrence4LeadingSquare_coeff_162
  recurrence4LeadingSquare_coeff_163
  recurrence4LeadingSquare_coeff_164
  recurrence4LeadingSquare_coeff_165
  recurrence4LeadingSquare_coeff_166
  recurrence4LeadingSquare_coeff_167
  recurrence4LeadingSquare_coeff_168

attribute [local simp]
  recurrence4LeadingSquare_coeff_169
  recurrence4LeadingSquare_coeff_170
  recurrence4LeadingSquare_coeff_171
  recurrence4LeadingSquare_coeff_172
  recurrence4LeadingSquare_coeff_173
  recurrence4LeadingSquare_coeff_174
  recurrence4LeadingSquare_coeff_175
  recurrence4LeadingSquare_coeff_176
  recurrence4LeadingSquare_coeff_177
  recurrence4LeadingSquare_coeff_178
  recurrence4LeadingSquare_coeff_179
  recurrence4LeadingSquare_coeff_180
  recurrence4LeadingSquare_coeff_181
  recurrence4LeadingSquare_coeff_182
  recurrence4LeadingSquare_coeff_183
  recurrence4LeadingSquare_coeff_184
  recurrence4LeadingSquare_coeff_185
  recurrence4LeadingSquare_coeff_186
  recurrence4LeadingSquare_coeff_187
  recurrence4LeadingSquare_coeff_188
  recurrence4LeadingSquare_coeff_189
  recurrence4LeadingSquare_coeff_190
  recurrence4LeadingSquare_coeff_191
  recurrence4LeadingSquare_coeff_192
  recurrence4LeadingSquare_coeff_193
  recurrence4LeadingSquare_coeff_194
  recurrence4LeadingSquare_coeff_195
  recurrence4LeadingSquare_coeff_196
  recurrence4LeadingSquare_coeff_197
  recurrence4LeadingSquare_coeff_198
  recurrence4LeadingSquare_coeff_199
  recurrence4LeadingSquare_coeff_200
  recurrence4LeadingSquare_coeff_201
  recurrence4LeadingSquare_coeff_202
  recurrence4LeadingSquare_coeff_203
  recurrence4LeadingSquare_coeff_204
  recurrence4LeadingSquare_coeff_205
  recurrence4LeadingSquare_coeff_206
  recurrence4LeadingSquare_coeff_207
  recurrence4LeadingSquare_coeff_208
  recurrence4LeadingSquare_coeff_209
  recurrence4LeadingSquare_coeff_210
  recurrence4LeadingSquare_coeff_211
  recurrence4LeadingSquare_coeff_212
  recurrence4LeadingSquare_coeff_213
  recurrence4LeadingSquare_coeff_214
  recurrence4LeadingSquare_coeff_215
  recurrence4LeadingSquare_coeff_216
  recurrence4LeadingSquare_coeff_217
  recurrence4LeadingSquare_coeff_218
  recurrence4LeadingSquare_coeff_219
  recurrence4LeadingSquare_coeff_220
  recurrence4LeadingSquare_coeff_221
  recurrence4LeadingSquare_coeff_222
  recurrence4LeadingSquare_coeff_223
  recurrence4LeadingSquare_coeff_224
  recurrence4LeadingSquare_coeff_225
  recurrence4LeadingSquare_coeff_226
  recurrence4LeadingSquare_coeff_227
  recurrence4LeadingSquare_coeff_228
  recurrence4LeadingSquare_coeff_229
  recurrence4LeadingSquare_coeff_230
  recurrence4LeadingSquare_coeff_231
  recurrence4LeadingSquare_coeff_232

attribute [local simp]
  recurrence4LeadingSquare_coeff_233
  recurrence4LeadingSquare_coeff_234
  recurrence4LeadingSquare_coeff_235
  recurrence4LeadingSquare_coeff_236
  recurrence4LeadingSquare_coeff_237
  recurrence4LeadingSquare_coeff_238
  recurrence4LeadingSquare_coeff_239
  recurrence4LeadingSquare_coeff_240
  recurrence4LeadingSquare_coeff_241
  recurrence4LeadingSquare_coeff_242
  recurrence4LeadingSquare_coeff_243
  recurrence4LeadingSquare_coeff_244
  recurrence4LeadingSquare_coeff_245
  recurrence4LeadingSquare_coeff_246
  recurrence4LeadingSquare_coeff_247
  recurrence4LeadingSquare_coeff_248
  recurrence4LeadingSquare_coeff_249
  recurrence4LeadingSquare_coeff_250
  recurrence4LeadingSquare_coeff_251
  recurrence4LeadingSquare_coeff_252
  recurrence4LeadingSquare_coeff_253
  recurrence4LeadingSquare_coeff_254
  recurrence4LeadingSquare_coeff_255
  recurrence4LeadingSquare_coeff_256
  recurrence4LeadingSquare_coeff_257
  recurrence4LeadingSquare_coeff_258
  recurrence4LeadingSquare_coeff_259
  recurrence4LeadingSquare_coeff_260
  recurrence4LeadingSquare_coeff_261
  recurrence4LeadingSquare_coeff_262
  recurrence4LeadingSquare_coeff_263
  recurrence4LeadingSquare_coeff_264
  recurrence4LeadingSquare_coeff_265
  recurrence4LeadingSquare_coeff_266
  recurrence4LeadingSquare_coeff_267
  recurrence4LeadingSquare_coeff_268
  recurrence4LeadingSquare_coeff_269
  recurrence4LeadingSquare_coeff_270
  recurrence4LeadingSquare_coeff_271
  recurrence4LeadingSquare_coeff_272
  recurrence4LeadingSquare_coeff_273
  recurrence4LeadingSquare_coeff_274
  recurrence4LeadingSquare_coeff_275
  recurrence4LeadingSquare_coeff_276
  recurrence4LeadingSquare_coeff_277
  recurrence4LeadingSquare_coeff_278
  recurrence4LeadingSquare_coeff_279
  recurrence4LeadingSquare_coeff_280
  recurrence4LeadingSquare_coeff_281
  recurrence4LeadingSquare_coeff_282
  recurrence4LeadingSquare_coeff_283
  recurrence4LeadingSquare_coeff_284
  recurrence4LeadingSquare_coeff_285
  recurrence4LeadingSquare_coeff_286
  recurrence4LeadingSquare_coeff_287
  recurrence4LeadingSquare_coeff_288
  recurrence4LeadingSquare_coeff_289
  recurrence4LeadingSquare_coeff_290
  recurrence4LeadingSquare_coeff_291
  recurrence4LeadingSquare_coeff_292
  recurrence4LeadingSquare_coeff_293
  recurrence4LeadingSquare_coeff_294
  recurrence4LeadingSquare_coeff_295
  recurrence4LeadingSquare_coeff_296

attribute [local simp]
  recurrence4LeadingSquare_coeff_297
  recurrence4LeadingSquare_coeff_298
  recurrence4LeadingSquare_coeff_299
  recurrence4LeadingSquare_coeff_300
  recurrence4LeadingSquare_coeff_301
  recurrence4LeadingSquare_coeff_302
  recurrence4LeadingSquare_coeff_303
  recurrence4LeadingSquare_coeff_304
  recurrence4LeadingSquare_coeff_305
  recurrence4LeadingSquare_coeff_306
  recurrence4LeadingSquare_coeff_307
  recurrence4LeadingSquare_coeff_308
  recurrence4LeadingSquare_coeff_309
  recurrence4LeadingSquare_coeff_310
  recurrence4LeadingSquare_coeff_311
  recurrence4LeadingSquare_coeff_312
  recurrence4LeadingSquare_coeff_313
  recurrence4LeadingSquare_coeff_314
  recurrence4LeadingSquare_coeff_315
  recurrence4LeadingSquare_coeff_316
  recurrence4LeadingSquare_coeff_317
  recurrence4LeadingSquare_coeff_318
  recurrence4LeadingSquare_coeff_319
  recurrence4LeadingSquare_coeff_320
  recurrence4LeadingSquare_coeff_321
  recurrence4LeadingSquare_coeff_322
  recurrence4LeadingSquare_coeff_323
  recurrence4LeadingSquare_coeff_324
  recurrence4LeadingSquare_coeff_325
  recurrence4LeadingSquare_coeff_326
  recurrence4LeadingSquare_coeff_327
  recurrence4LeadingSquare_coeff_328
  recurrence4LeadingSquare_coeff_38
  recurrence4LeadingSquare_coeff_39
  recurrence4LeadingSquare_coeff_40
  recurrence4LeadingSquare_coeff_41
  recurrence4LeadingSquare_coeff_42
  recurrence4LeadingSquare_coeff_43
  recurrence4LeadingSquare_coeff_44
  recurrence4LeadingSquare_coeff_45
  recurrence4LeadingSquare_coeff_46
  recurrence4LeadingSquare_coeff_47
  recurrence4LeadingSquare_coeff_48
  recurrence4LeadingSquare_coeff_49
  recurrence4LeadingSquare_coeff_50
  recurrence4LeadingSquare_coeff_51
  recurrence4LeadingSquare_coeff_52
  recurrence4LeadingSquare_coeff_53
  recurrence4LeadingSquare_coeff_54
  recurrence4LeadingSquare_coeff_55
  recurrence4LeadingSquare_coeff_56
  recurrence4LeadingSquare_coeff_57
  recurrence4LeadingSquare_coeff_58
  recurrence4LeadingSquare_coeff_59
  recurrence4LeadingSquare_coeff_60
  recurrence4LeadingSquare_coeff_61
  recurrence4LeadingSquare_coeff_62
  recurrence4LeadingSquare_coeff_63
  recurrence4LeadingSquare_coeff_64
  recurrence4LeadingSquare_coeff_65
  recurrence4LeadingSquare_coeff_66
  recurrence4LeadingSquare_coeff_67
  recurrence4LeadingSquare_coeff_68
  recurrence4LeadingSquare_coeff_69

attribute [local simp]
  recurrence4LeadingSquare_coeff_70
  recurrence4LeadingSquare_coeff_71
  recurrence4LeadingSquare_coeff_72
  recurrence4LeadingSquare_coeff_73
  recurrence4LeadingSquare_coeff_74
  recurrence4LeadingSquare_coeff_75
  recurrence4LeadingSquare_coeff_76
  recurrence4LeadingSquare_coeff_77
  recurrence4LeadingSquare_coeff_78
  recurrence4LeadingSquare_coeff_79
  recurrence4LeadingSquare_coeff_80
  recurrence4LeadingSquare_coeff_81
  recurrence4LeadingSquare_coeff_82
  recurrence4LeadingSquare_coeff_83
  recurrence4LeadingSquare_coeff_84
  recurrence4LeadingSquare_coeff_85
  recurrence4LeadingSquare_coeff_86
  recurrence4LeadingSquare_coeff_87
  recurrence4LeadingSquare_coeff_88
  recurrence4LeadingSquare_coeff_89
  recurrence4LeadingSquare_coeff_90
  recurrence4LeadingSquare_coeff_91
  recurrence4LeadingSquare_coeff_92
  recurrence4LeadingSquare_coeff_93
  recurrence4LeadingSquare_coeff_94
  recurrence4LeadingSquare_coeff_95
  recurrence4LeadingSquare_coeff_96
  recurrence4LeadingSquare_coeff_97
  recurrence4LeadingSquare_coeff_98
  recurrence4LeadingSquare_coeff_99

private theorem recurrence4Scalar2Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (224 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_224 :
    recurrence4Scalar2Left.coeff 224 =
      (((((43713348310941711029886566 * 10 ^ 70 +
        9211634317458810002590308080374325330426837409373061844159531510212746) * 10 ^ 70 +
        1776973073504648114471628270029356267609944563241521852048165225882492) * 10 ^ 70 +
        9019256021498525349185950610139089520080731151512944884152781858082433) * 10 ^ 70 +
        3982785633793867575155578110563627185775392780908051974729104375722318) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (224 - x)) = _
  rw [show 225 = 38 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (225 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_225 :
    recurrence4Scalar2Left.coeff 225 =
      -(((((61969834068041524867765790 * 10 ^ 70 +
        5024361493784141104989258399420625204191238002530612427799503849853251) * 10 ^ 70 +
        6918570619061017380915546544585090748384075628454084933255308544886207) * 10 ^ 70 +
        3972261941829526366955122315809094378298389682040128300785797274438771) * 10 ^ 70 +
        0301757347966346141043425203830848166697899407881695704188074044998141) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (225 - x)) = _
  rw [show 226 = 39 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (226 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_226 :
    recurrence4Scalar2Left.coeff 226 =
      (((((86558904241616799455909503 * 10 ^ 70 +
        5265752200488778072558149277663563512145170899097576960943123469923290) * 10 ^ 70 +
        3322558613520124043661798053769656792625610929295564829488206477126742) * 10 ^ 70 +
        8727672437430430190180561237636720346204446506319614548022260793009446) * 10 ^ 70 +
        7736619496092048689215270869832367351535004920402418885903237506363166) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (226 - x)) = _
  rw [show 227 = 40 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (227 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_227 :
    recurrence4Scalar2Left.coeff 227 =
      -(((((119115972437275299518055871 * 10 ^ 70 +
        3780456989521618376252929962161998846489332545298422684423562518510464) * 10 ^ 70 +
        3489945256526155515551363173578007089593416059315128342221273726390183) * 10 ^ 70 +
        1519510156648965918744388228934765301339497587953812662719444471873799) * 10 ^ 70 +
        4233869448950139888270415627812587806868645957285148417434938343194433) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (227 - x)) = _
  rw [show 228 = 41 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (228 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_228 :
    recurrence4Scalar2Left.coeff 228 =
      (((((161477589371047885984768901 * 10 ^ 70 +
        0461113284954424356950094648944251286381125334484632547208230977129856) * 10 ^ 70 +
        8054576499582488184517068983137696735928764238638969400637685010393443) * 10 ^ 70 +
        7030147854106563649641766036794864296096896331534971050293443914828736) * 10 ^ 70 +
        1963179183791408355147839892810707150160097330684028328765616611267942) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (228 - x)) = _
  rw [show 229 = 42 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (229 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_229 :
    recurrence4Scalar2Left.coeff 229 =
      -(((((215620769237615185238627315 * 10 ^ 70 +
        8405059768378401876940177226202243668606153988652667315255792731887257) * 10 ^ 70 +
        9355699993432371154728897135818870465930118486030737386332105717758109) * 10 ^ 70 +
        1436407964563777946800436935792951109762369145628227082322176795122620) * 10 ^ 70 +
        9977180004948302054229023515897223456877581778715356560151638746832754) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (229 - x)) = _
  rw [show 230 = 43 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (230 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_230 :
    recurrence4Scalar2Left.coeff 230 =
      (((((283564108626537153466371184 * 10 ^ 70 +
        4275430818346467850508390684150776439845603409441787353743462565790942) * 10 ^ 70 +
        9152826448936603075285762154767065224494312395718470379732091906315571) * 10 ^ 70 +
        0885744778377697037116219112129145888123422975401600085112235828820059) * 10 ^ 70 +
        5662785956252985403609162521455703566343160238301778304922272206041230) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (230 - x)) = _
  rw [show 231 = 44 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_230_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (231 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_231 :
    recurrence4Scalar2Left.coeff 231 =
      -(((((367226372116469399506711265 * 10 ^ 70 +
        3814823130088074475381606833220685986262376765991350237231282087674479) * 10 ^ 70 +
        3314307955853246629388387941312809606714861151392734570236869294687486) * 10 ^ 70 +
        1887843677752603128637667101541345003167425982330381657500053439518643) * 10 ^ 70 +
        9714775165091235590871594958939058039798326497109109843957921314995792) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (231 - x)) = _
  rw [show 232 = 45 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_231_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (232 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_232 :
    recurrence4Scalar2Left.coeff 232 =
      (((((468241937611233227690014790 * 10 ^ 70 +
        8804926584946048192857152014604349910847077678415581909874949983036779) * 10 ^ 70 +
        9155849917334599078465087655666077076159432650084677972634357036075541) * 10 ^ 70 +
        5219470095097029766241102481935972312992600782622782517248947149082035) * 10 ^ 70 +
        6931135929925332771616230292750705154899232886473078922533716585329494) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (232 - x)) = _
  rw [show 233 = 46 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_232_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (233 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_233 :
    recurrence4Scalar2Left.coeff 233 =
      -(((((587737742746738005730854490 * 10 ^ 70 +
        2178324772139692591633423286421179729210262963019341919223079526063273) * 10 ^ 70 +
        8041915929604862578742650209337624010815417083803840893001611095458729) * 10 ^ 70 +
        7135060205010499377168917947156401272668318678683585708753123377594239) * 10 ^ 70 +
        0356092939172080274228026804711211791859781817376409392847639656412673) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (233 - x)) = _
  rw [show 234 = 47 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_233_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (234 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_234 :
    recurrence4Scalar2Left.coeff 234 =
      (((((726082901517734937715152873 * 10 ^ 70 +
        2226793861485421921298935486330824769678338196999026094707890862193880) * 10 ^ 70 +
        3910560155306681139072219975292759203180271451231803258342325716232723) * 10 ^ 70 +
        2111454638478571615213014801294837117851150874846204890719960982965441) * 10 ^ 70 +
        2315943953233667205259142653772682378604419033314825824780753606749028) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (234 - x)) = _
  rw [show 235 = 48 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_234_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (235 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_235 :
    recurrence4Scalar2Left.coeff 235 =
      -(((((882629403114047542458613015 * 10 ^ 70 +
        3017913315619241152128950967377474180650065595492208094614686244249373) * 10 ^ 70 +
        9906573958538961934839390865887393801066617364777833365235039219802784) * 10 ^ 70 +
        1781293800655403365071157775511977851957308531013866802653745554605439) * 10 ^ 70 +
        9326642336255715583732063860142527971121152809830854751454316451235206) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (235 - x)) = _
  rw [show 236 = 49 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_235_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (236 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_236 :
    recurrence4Scalar2Left.coeff 236 =
      (((((1055469374894554551284550021 * 10 ^ 70 +
        3221116249278156045704277019044989542244852115702696108630049444273711) * 10 ^ 70 +
        7117605423222794221331598692670556582575184560902636003608369766078006) * 10 ^ 70 +
        0078828879953461119561727331993083865068440719668334806048164754971598) * 10 ^ 70 +
        7679756179822854458454814265952573900434468820125900981369156403625400) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (236 - x)) = _
  rw [show 237 = 50 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_236_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (237 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_237 :
    recurrence4Scalar2Left.coeff 237 =
      -(((((1241240130869522185500325847 * 10 ^ 70 +
        6041581604063594203472383867363915095173644098934951114684863182929156) * 10 ^ 70 +
        8036835112726600458489895623404118438191507802458626922484432346367079) * 10 ^ 70 +
        5647577194265050810835510577462949614466396221721117265579023354239675) * 10 ^ 70 +
        3444119915377714066285636640536176818158525842340067496085710308840596) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (237 - x)) = _
  rw [show 238 = 51 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_237_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (238 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_238 :
    recurrence4Scalar2Left.coeff 238 =
      (((((1435011334904437747521410807 * 10 ^ 70 +
        8054646861308648893421481179795184041474608667835613377628261391090089) * 10 ^ 70 +
        4667273452190449305271858617315505067938424311446943202874391376248615) * 10 ^ 70 +
        5586413803461757807885548219183305722969398623892068976243510789398435) * 10 ^ 70 +
        7541716011053717071289942274246531444144936026253233049839560194759561) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (238 - x)) = _
  rw [show 239 = 52 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_238_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (239 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_239 :
    recurrence4Scalar2Left.coeff 239 =
      -(((((1630287834941949198743874053 * 10 ^ 70 +
        4149771512374299466472238665895153988299824892302002690531687213522612) * 10 ^ 70 +
        5418337928710626754732124621347662707380882840785177518278269626132803) * 10 ^ 70 +
        6074206894861974943374398027711591875474816475249460987903612900041471) * 10 ^ 70 +
        6513200961160292786903398278134093322586480597236199100371582551372645) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (239 - x)) = _
  rw [show 240 = 53 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_239_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (240 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_240 :
    recurrence4Scalar2Left.coeff 240 =
      (((((1819156118351602709347500307 * 10 ^ 70 +
        6893491553861499748934497853283950030534167959829427931370286515852895) * 10 ^ 70 +
        5620101524416482955835637274798347067620162711414565552848743806417103) * 10 ^ 70 +
        9485242904846958257013819665458285048399102836289594867822120210455588) * 10 ^ 70 +
        5002786871828945131087980600314505791261123243667438727300333419342870) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (240 - x)) = _
  rw [show 241 = 54 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_240_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (241 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_241 :
    recurrence4Scalar2Left.coeff 241 =
      -(((((1992591499762041094625961940 * 10 ^ 70 +
        6224954090339847342570528348395146136126549650027618621636869903957884) * 10 ^ 70 +
        3005051777394123728609294044060467898014022785595551092612728262809178) * 10 ^ 70 +
        1117705980696183989337327440099193356913351927904772834979268037590526) * 10 ^ 70 +
        6436090451981775273414795428800936003810493845767383105038660563821174) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (241 - x)) = _
  rw [show 242 = 55 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_241_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (242 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_242 :
    recurrence4Scalar2Left.coeff 242 =
      (((((2140927452847794199639252999 * 10 ^ 70 +
        0828779819804414799437143592592955444215607732284847299766531246545852) * 10 ^ 70 +
        5256720909783715539484442025466623847695927683448824200681635284087943) * 10 ^ 70 +
        0883826459581385779354347278447961085367657267728250945529758298038561) * 10 ^ 70 +
        9515346060230606054853046459254170967363569756652675400014762794037752) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (242 - x)) = _
  rw [show 243 = 56 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_242_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (243 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_243 :
    recurrence4Scalar2Left.coeff 243 =
      -(((((2254469201170907087450092379 * 10 ^ 70 +
        4008953440297594275569344687103570598161780381137566981467441803394243) * 10 ^ 70 +
        5336781105281871635686616760495560233944428818974096073128596158049168) * 10 ^ 70 +
        5269368854633236510613974140937086980848705816067567506577379271739667) * 10 ^ 70 +
        7882149973478025871089224524381115222055927991776089035079423554232684) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (243 - x)) = _
  rw [show 244 = 57 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_243_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (244 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_244 :
    recurrence4Scalar2Left.coeff 244 =
      (((((2324212926385387174027347619 * 10 ^ 70 +
        3717202021479993128733750469431715182657173736594397417027913512382787) * 10 ^ 70 +
        5375350448541012565215038032012173536004203239458633336789123074750304) * 10 ^ 70 +
        5771550791158888934320496338849442926153855518513727151833188561192907) * 10 ^ 70 +
        3181195953306511624679599940695520086307024199045472499742749798526020) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (244 - x)) = _
  rw [show 245 = 58 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_244_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (245 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_245 :
    recurrence4Scalar2Left.coeff 245 =
      -(((((2342612547469146563513918720 * 10 ^ 70 +
        2382499778009754268311379428777277061520399256933253527044419787364432) * 10 ^ 70 +
        2176825721693697043835704426296862697705462127096281375985541958247629) * 10 ^ 70 +
        6891800792535296051603475821538764457247618446561487249489438372272906) * 10 ^ 70 +
        1474322947320407895760454192010278296531337891387156017589088012326112) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (245 - x)) = _
  rw [show 246 = 59 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_245_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (246 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_246 :
    recurrence4Scalar2Left.coeff 246 =
      (((((2304321095952665967745507389 * 10 ^ 70 +
        1051164549047456846010647679140176770504521651064031481285995033092476) * 10 ^ 70 +
        9513639828494962920309382358397360230343712237775462541783484655471151) * 10 ^ 70 +
        6484442882811809442607160175920341331201142767789194687548861655446467) * 10 ^ 70 +
        1732763231873813834326696614833127919638658266782795219650646229739212) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (246 - x)) = _
  rw [show 247 = 60 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_246_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (247 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_247 :
    recurrence4Scalar2Left.coeff 247 =
      -(((((2206826199628609873298861761 * 10 ^ 70 +
        1243564476875550583057513607221678248672243465776799968114651903653933) * 10 ^ 70 +
        8451171235249952454311704228151131950342520120027752172326682507094622) * 10 ^ 70 +
        5369526241572160933156835081893016376780811703583291595361147072826834) * 10 ^ 70 +
        4782343796027057116832025006645615158702822123693990839041564649686522) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (247 - x)) = _
  rw [show 248 = 61 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_247_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (248 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_248 :
    recurrence4Scalar2Left.coeff 248 =
      (((((2050901300474051242228291057 * 10 ^ 70 +
        8916227293672362504272169921225532611687117480428765368623257545083867) * 10 ^ 70 +
        1902429904568547902753275442318343394351507381466930123140427142151763) * 10 ^ 70 +
        1556332629130009402667237963438197236937132859257207953434852574053510) * 10 ^ 70 +
        0881879753862814133886159641161345952426277535789734524007496557314875) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (248 - x)) = _
  rw [show 249 = 62 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_248_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (249 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_249 :
    recurrence4Scalar2Left.coeff 249 =
      -(((((1840806952846364533459021638 * 10 ^ 70 +
        3598063070441460594577118381720415603440885625209889740236911032183517) * 10 ^ 70 +
        1047134344407489007840181044364182779591092052961606416304474415975333) * 10 ^ 70 +
        1246564873637978889277258589462102416048959888208891570960778910344505) * 10 ^ 70 +
        3786258028609977852974657547544671738176174911155735124984129575154671) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (249 - x)) = _
  rw [show 250 = 63 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_249_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (250 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_250 :
    recurrence4Scalar2Left.coeff 250 =
      (((((1584199289116863570298556929 * 10 ^ 70 +
        5086595768798353813223467530659195964466539127587570917170278889465928) * 10 ^ 70 +
        2560929755353029789114471690380868717235190151986172919224892680496549) * 10 ^ 70 +
        1861780021290055769875564417366199107097472508626296853549375242011213) * 10 ^ 70 +
        5397913036560204096651738469845151025449156576278775042535060729946896) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (250 - x)) = _
  rw [show 251 = 64 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_250_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (251 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_251 :
    recurrence4Scalar2Left.coeff 251 =
      -(((((1291733256602709092571248640 * 10 ^ 70 +
        1321132161980901178954492667146077598522425154074413679435077425951213) * 10 ^ 70 +
        9284559266745295072363641375672981907473966662433131433277328427361272) * 10 ^ 70 +
        9365669438955622249901344657803576749187545817041773787263108739111758) * 10 ^ 70 +
        6794284724998276337928071594410095961398002219007642562922150392452811) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (251 - x)) = _
  rw [show 252 = 65 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_251_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (252 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_252 :
    recurrence4Scalar2Left.coeff 252 =
      (((((976382824342982504098135041 * 10 ^ 70 +
        2943052770362454794457411338561854866863685834979872558033489343599084) * 10 ^ 70 +
        3943082497076949935198615170617038842643563059220445974293198170582580) * 10 ^ 70 +
        9226648648125806062552684083258031628229682462613829314428825600992350) * 10 ^ 70 +
        7344387780905573337038201184930722356985813393569938275858474480353999) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (252 - x)) = _
  rw [show 253 = 66 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_252_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (253 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_253 :
    recurrence4Scalar2Left.coeff 253 =
      -(((((652534377074405961980658208 * 10 ^ 70 +
        2435118354393435837865204657324080296813939029892327991025349798267661) * 10 ^ 70 +
        0608415013432509602688280391082810636068746132332024197863808271919894) * 10 ^ 70 +
        1653280034328023281551270510505946709392384771277859442074811506269927) * 10 ^ 70 +
        1575504271086586443226610605801687494794437719908550399374328927428224) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (253 - x)) = _
  rw [show 254 = 67 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_253_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (254 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_254 :
    recurrence4Scalar2Left.coeff 254 =
      (((((334938062463434872848814408 * 10 ^ 70 +
        9533982400940869365815919570504665205552081098004516030785433827751192) * 10 ^ 70 +
        9901205191627269155717825618737473003914519728425230348921503594875129) * 10 ^ 70 +
        2266755132604873837899057658121772118701922536797872798785853014955747) * 10 ^ 70 +
        2121413681562463111997917370391696422238633191020476988389225223837760) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (254 - x)) = _
  rw [show 255 = 68 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_254_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (255 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_255 :
    recurrence4Scalar2Left.coeff 255 =
      -(((((37620614741561204451759294 * 10 ^ 70 +
        5642487074638888501403961071643403016194675852365705093050721332548453) * 10 ^ 70 +
        6232303819370834653556730783110318273996778047562551016377416257414293) * 10 ^ 70 +
        1280447625215077742931211139835908156393110613955863366021078948109063) * 10 ^ 70 +
        6036213086314133180217993924244566527993407390373987018681704384159935) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (255 - x)) = _
  rw [show 256 = 69 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_255_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (256 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_256 :
    recurrence4Scalar2Left.coeff 256 =
      -(((((227130847368538821269660653 * 10 ^ 70 +
        5022855634905132940824666469760050811252449090963874888637859098704546) * 10 ^ 70 +
        7749595614818519795500029069916721333903059391442290836330522963571386) * 10 ^ 70 +
        4311213069071949039554484434246430882318859973870497221024421661097292) * 10 ^ 70 +
        6622329098932948957700952836137366979835814091006408633726142644893309) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (256 - x)) = _
  rw [show 257 = 70 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_256_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (257 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_257 :
    recurrence4Scalar2Left.coeff 257 =
      (((((449612465598788596452860862 * 10 ^ 70 +
        4246569645849295661668189328657499445830087890754727861435564527180580) * 10 ^ 70 +
        2944683623539420781433924050398877340934615941326939638591023614972926) * 10 ^ 70 +
        5363180218472880430084123990267586579666875493025148144050045148407307) * 10 ^ 70 +
        2463982957419200265180358262895771628945543220791533255046505603200974) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (257 - x)) = _
  rw [show 258 = 71 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_257_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (258 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_258 :
    recurrence4Scalar2Left.coeff 258 =
      -(((((623293944478287106108627292 * 10 ^ 70 +
        2017371459759148928384062475962306042634874628256348295076103630528366) * 10 ^ 70 +
        6740665037215540877136247246249213514534515581666505981670495793715498) * 10 ^ 70 +
        3524806208155759254882717705140049978228188506900477758010282740080716) * 10 ^ 70 +
        4406317138868362404105126802336764747709237741955490663638214124760569) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (258 - x)) = _
  rw [show 259 = 72 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_258_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (259 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_259 :
    recurrence4Scalar2Left.coeff 259 =
      (((((745105425720720285176754944 * 10 ^ 70 +
        1042285951494587144220998301905695694348348425733516929256252085465076) * 10 ^ 70 +
        0204437735025303823263593747407708049412561147926472774670264724335808) * 10 ^ 70 +
        8753982213102303125995110382570271004404848361636127428289721370052489) * 10 ^ 70 +
        4098999361567330261467376069250538306054212220140310640475739190928295) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (259 - x)) = _
  rw [show 260 = 73 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_259_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (260 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_260 :
    recurrence4Scalar2Left.coeff 260 =
      -(((((815406996075062416622444584 * 10 ^ 70 +
        0659740112520904219161355399804719635635500373264683200387790010712641) * 10 ^ 70 +
        6283433070557479105397511075296883200453194358431239728987530757354061) * 10 ^ 70 +
        1889923722950531713752764780962456461459306290135986787727724742031896) * 10 ^ 70 +
        7264499618372504156647543169231936386089272549081441776564118222710905) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (260 - x)) = _
  rw [show 261 = 74 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_260_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (261 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_261 :
    recurrence4Scalar2Left.coeff 261 =
      (((((837663305172459654529748294 * 10 ^ 70 +
        0445156403594879554185600683522422643573876540369998312272623367379552) * 10 ^ 70 +
        5209650587592549267655411725807440140576360206298436218562704622906821) * 10 ^ 70 +
        2243262808659096910270224840316675313705470095834400497272648955063430) * 10 ^ 70 +
        5658729491507708377855433119406804389524227902780518430869693293998895) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (261 - x)) = _
  rw [show 262 = 75 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_261_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (262 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_262 :
    recurrence4Scalar2Left.coeff 262 =
      -(((((817877420232919413728264532 * 10 ^ 70 +
        9969429710333159656724885125991986724457827123834689682586943923930525) * 10 ^ 70 +
        3419859542443618447234342126566984987642718432592220972931009745343776) * 10 ^ 70 +
        4103697291943484980690060715491099989166126509416093283865528705056136) * 10 ^ 70 +
        6445828274918419670972378914029325802828966255792217919432767353807792) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (262 - x)) = _
  rw [show 263 = 76 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_262_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (263 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_263 :
    recurrence4Scalar2Left.coeff 263 =
      (((((763860856185412983286371006 * 10 ^ 70 +
        7471657330883190399789812200796883659675875948766838212906420291110090) * 10 ^ 70 +
        5687179094618332929087903434894672172999637290812222139609426870884804) * 10 ^ 70 +
        7041985837764637284455535620389966796762676288588284479658165411272160) * 10 ^ 70 +
        9300242519567959606948293963320261452772649249200137040961968183199752) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (263 - x)) = _
  rw [show 264 = 77 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_263_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (264 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_264 :
    recurrence4Scalar2Left.coeff 264 =
      -(((((684428188266827745715029805 * 10 ^ 70 +
        0007180712813478105877838293408993085004959717890631446019707281464928) * 10 ^ 70 +
        8415626357576365930674179374846274646793056306942881086212184114685524) * 10 ^ 70 +
        9564421884296758660178176402196494790161165541084677271074185389662149) * 10 ^ 70 +
        1000821123218295339431576498570536678014119738709681737409098573432705) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (264 - x)) = _
  rw [show 265 = 78 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_264_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (265 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_265 :
    recurrence4Scalar2Left.coeff 265 =
      (((((588604146434267094195278449 * 10 ^ 70 +
        5470722690375374217105549192040209100994605522331090090658181823338050) * 10 ^ 70 +
        7300513851014579561456663533110869253099271851098141253996617714560218) * 10 ^ 70 +
        6535280028090438417083900405571494867854214365797676714604605972636266) * 10 ^ 70 +
        7225511788085231813051509658002310931166201789389316183144518946034556) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (265 - x)) = _
  rw [show 266 = 79 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_265_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (266 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_266 :
    recurrence4Scalar2Left.coeff 266 =
      -(((((484919802426364505854535777 * 10 ^ 70 +
        5659235572965577003591662962190603534832298874935441475823114205186026) * 10 ^ 70 +
        4887830132364199623088957534908121387102933816341111672598817038231619) * 10 ^ 70 +
        0415668067031967601297892173949584491731908695677633830456038289395208) * 10 ^ 70 +
        4344051731006922581815520728296716472119618038990179503735748887889378) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (266 - x)) = _
  rw [show 267 = 80 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_266_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (267 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_267 :
    recurrence4Scalar2Left.coeff 267 =
      (((((380855060403807159728191676 * 10 ^ 70 +
        9084945672012643509151023180379920501059495725733701072249527324684052) * 10 ^ 70 +
        3374591963334432948336564781375822834442477736086035382359226259284864) * 10 ^ 70 +
        6228926172405666422342593751104770971980467868632430852312931173381601) * 10 ^ 70 +
        6765731808701473211794156557641210498382968470427759649281883369831429) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (267 - x)) = _
  rw [show 268 = 81 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_267_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (268 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_268 :
    recurrence4Scalar2Left.coeff 268 =
      -(((((282460719628668577513333725 * 10 ^ 70 +
        5077758695279105748241705794089829015498245577961339419994779900086829) * 10 ^ 70 +
        4359220462204603374558571838204165740544088353529113539714565271845846) * 10 ^ 70 +
        7273270949934562881447687456014358523535000166267396187915208134113601) * 10 ^ 70 +
        0368678765231558129525312860335061902241618489343297208250801965925485) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (268 - x)) = _
  rw [show 269 = 82 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_268_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (269 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_269 :
    recurrence4Scalar2Left.coeff 269 =
      (((((194168693384062568161112836 * 10 ^ 70 +
        8450091853270817393402994877152064034692452872009436231610340908994241) * 10 ^ 70 +
        2521394895165675815089264744685353510843420895034235788641893082982176) * 10 ^ 70 +
        9726863239306676701565626733665193190788447788232056315408847762746303) * 10 ^ 70 +
        5120699943173519370847161795684628237104848107215157112331350658022677) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (269 - x)) = _
  rw [show 270 = 83 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_269_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (270 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_270 :
    recurrence4Scalar2Left.coeff 270 =
      -(((((118776946138588391647861703 * 10 ^ 70 +
        1613563932469574295308131026991837660242524106813696973164494952309146) * 10 ^ 70 +
        2314622329018280170048449065254694378399669694315668501943584449482710) * 10 ^ 70 +
        8845275257804322077389946142758872715612451435569015891014576037677234) * 10 ^ 70 +
        3680593077249993203991074549511665740698248868163858409188513336122018) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (270 - x)) = _
  rw [show 271 = 84 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_270_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (271 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_271 :
    recurrence4Scalar2Left.coeff 271 =
      (((((57578876915072175515328543 * 10 ^ 70 +
        3852652407564879794402708688623270809120962808720938791398822298949288) * 10 ^ 70 +
        7326835204642171831426896060375486559807436550179614786592556693740821) * 10 ^ 70 +
        7740065317468197690191062742404132529858933552847144299065337461576511) * 10 ^ 70 +
        3102869140130965689196833307523060314912624278191943157021808754341026) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (271 - x)) = _
  rw [show 272 = 85 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_271_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (272 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_272 :
    recurrence4Scalar2Left.coeff 272 =
      -(((((10596613640910538938590846 * 10 ^ 70 +
        6696196897217580406984030249218294398388577214059059806466028940372782) * 10 ^ 70 +
        2912427553941814217499991255515238308225254409174857919476077321756027) * 10 ^ 70 +
        2799044984835467914770641474524351482371426197331445378482192098147243) * 10 ^ 70 +
        7303510515680795460481892429408328265812995185897430310385613697233305) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (272 - x)) = _
  rw [show 273 = 86 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_272_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (273 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_273 :
    recurrence4Scalar2Left.coeff 273 =
      -(((((23125803389655357949876720 * 10 ^ 70 +
        4738908338777047027077507613243633680406248949245878135213564099493154) * 10 ^ 70 +
        5915571096019516406257296593291624807321496899279125595341229681057697) * 10 ^ 70 +
        3642454211004799629993250634220559893818062391541315744816906865928215) * 10 ^ 70 +
        3720107693253918078047118911623153803266899495893446903821544543010838) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (273 - x)) = _
  rw [show 274 = 87 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_273_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (274 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_274 :
    recurrence4Scalar2Left.coeff 274 =
      (((((45210883936938392753701905 * 10 ^ 70 +
        2205510956782540426054457239031746517386280900920306955782118505323180) * 10 ^ 70 +
        1684035566579342761454190493714266141292430390139516178179091206105319) * 10 ^ 70 +
        8313283775024903125913369897060837479836169894773385173132675292863831) * 10 ^ 70 +
        3477038520033396823859379670751634997957678621224807453492678891808795) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (274 - x)) = _
  rw [show 275 = 88 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_274_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (275 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_275 :
    recurrence4Scalar2Left.coeff 275 =
      -(((((57652375597862623522217374 * 10 ^ 70 +
        9497727295556199919038448131945494389119213936231604431518250895105893) * 10 ^ 70 +
        6058184454688257810794650040510106421314072500174655865088640167082086) * 10 ^ 70 +
        3623787673765516624105772668624515132661642673052389270396694151730306) * 10 ^ 70 +
        6388265579014649902660999952094218603772563670097108102787930974159465) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (275 - x)) = _
  rw [show 276 = 89 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_275_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (276 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_276 :
    recurrence4Scalar2Left.coeff 276 =
      (((((62561172602217601732976356 * 10 ^ 70 +
        6876909675585656452532676633398620099202179443461578079719115242589892) * 10 ^ 70 +
        3038835895027648871798247474664456415293002166147636202346179644718639) * 10 ^ 70 +
        2466491610477239799270034101402895594240461198462995162133497204656739) * 10 ^ 70 +
        2611905257824030772726579584307376445514793742234048040666420078493165) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (276 - x)) = _
  rw [show 277 = 90 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_276_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (277 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_277 :
    recurrence4Scalar2Left.coeff 277 =
      -(((((61967054809696525318348391 * 10 ^ 70 +
        0847152700974621155085400020208884748369506054520229360004219353080482) * 10 ^ 70 +
        4061979626177829980153013173953104807082584818363942363437343968784641) * 10 ^ 70 +
        6904996392604606353111064517224169354440239126435571425397516900430986) * 10 ^ 70 +
        7158538384528211674128226272863265052163410973991109628340025819497681) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (277 - x)) = _
  rw [show 278 = 91 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_277_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (278 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_278 :
    recurrence4Scalar2Left.coeff 278 =
      (((((57681212342988105233159483 * 10 ^ 70 +
        4615706214489629259702901912129387375812970520397901283081215395297242) * 10 ^ 70 +
        9335247178685789153568417893311655429330126375231184017434230945734869) * 10 ^ 70 +
        8952540631124723264155342499079945811246959700459714453367050542627041) * 10 ^ 70 +
        1619618812945616849172420605867133726047516594149223236320510860437578) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (278 - x)) = _
  rw [show 279 = 92 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_278_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (279 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_279 :
    recurrence4Scalar2Left.coeff 279 =
      -(((((51216666802728196560820766 * 10 ^ 70 +
        0450229871572831244370173047030169699643317113079528572758920751905164) * 10 ^ 70 +
        9015076049260109086454877156613192380533889255676673685577715491008315) * 10 ^ 70 +
        3877779069313311169383023978665265890603112303834716764409556346265620) * 10 ^ 70 +
        0386233569146113995276055174933188796188882482543281528843760473574452) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (279 - x)) = _
  rw [show 280 = 93 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_279_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (280 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_280 :
    recurrence4Scalar2Left.coeff 280 =
      (((((43758226914032361474920643 * 10 ^ 70 +
        3199207919737012884716080178182906841229032751476412449496642931328656) * 10 ^ 70 +
        3705597219679087814191717650869128923785229628980653658268461981363211) * 10 ^ 70 +
        0618784452331847993841125051889529688292546526632760739426888946936087) * 10 ^ 70 +
        4497089492543136751722838456736848477411887989753065085247807036048651) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (280 - x)) = _
  rw [show 281 = 94 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_280_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (281 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_281 :
    recurrence4Scalar2Left.coeff 281 =
      -(((((36170603433059040155967069 * 10 ^ 70 +
        1270469301155999919649615193990280517812847237827579709243970339830326) * 10 ^ 70 +
        2089679548538105700423718081569793103228047004945711069474125605592748) * 10 ^ 70 +
        4460773490856863244081545990667220411451780502713938559902951046051503) * 10 ^ 70 +
        2266431802364242478366016996163196616173799058016878895279195077358810) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (281 - x)) = _
  rw [show 282 = 95 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_281_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (282 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_282 :
    recurrence4Scalar2Left.coeff 282 =
      (((((29032477681655414858353121 * 10 ^ 70 +
        8966367783368371315516232773304545036403417159791086463880127649003350) * 10 ^ 70 +
        1581594967058051457519277370035016223949530933299766077515196150286980) * 10 ^ 70 +
        3771231487708719668781454225517786398346353666927324564800370253340916) * 10 ^ 70 +
        3657493771268228704384781924199654027459529076556503858371064287296312) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (282 - x)) = _
  rw [show 283 = 96 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_282_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (283 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_283 :
    recurrence4Scalar2Left.coeff 283 =
      -(((((22685164982675840344968713 * 10 ^ 70 +
        7766063035355633494318408104016514403997334225899640250870019903875353) * 10 ^ 70 +
        4370402915054742365921380914375357940799865818288082438387261544906017) * 10 ^ 70 +
        3642640559847283144282756099209818967314786606504032355286142082658849) * 10 ^ 70 +
        2080555318986756401540967107169539537471222616967271576797805410395781) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (283 - x)) = _
  rw [show 284 = 97 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_283_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (284 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_284 :
    recurrence4Scalar2Left.coeff 284 =
      (((((17286443590494531228099684 * 10 ^ 70 +
        7691899000045201366981274190112366967214769293032177767821017314546204) * 10 ^ 70 +
        4941901417219064137411959077035925104745265038422202936847306291215020) * 10 ^ 70 +
        2817614365774668179196071637046030248879149022950639493273152389177870) * 10 ^ 70 +
        9743647434460274963995200599965296975155154072813588643123010323325845) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (284 - x)) = _
  rw [show 285 = 98 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_284_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (285 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_285 :
    recurrence4Scalar2Left.coeff 285 =
      -(((((12862560754128589287683682 * 10 ^ 70 +
        9481573571875942619947761665134624217798715278137432431959653805738326) * 10 ^ 70 +
        3448074152476267578699724867744272291964321175535280559898745185431378) * 10 ^ 70 +
        8732273920859819287500210758174588145404204499237301779775853857717658) * 10 ^ 70 +
        7824975210920765365987784997565677756910341821692158655033978495773637) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (285 - x)) = _
  rw [show 286 = 99 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_285_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (286 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_286 :
    recurrence4Scalar2Left.coeff 286 =
      (((((9353911301154453926786167 * 10 ^ 70 +
        2610399137814125838027166355392172272576954930669416217910011982286733) * 10 ^ 70 +
        9860281999391654947493896940438660721091204548701246004463989957669082) * 10 ^ 70 +
        2517995044712549290635610670307847453870564907787269169988260899162598) * 10 ^ 70 +
        4946037995979948271718050038854792614422502550602005402487352274239101) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (286 - x)) = _
  rw [show 287 = 100 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_286_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (287 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_287 :
    recurrence4Scalar2Left.coeff 287 =
      -(((((6652081632201668586155066 * 10 ^ 70 +
        9272745163868286375702470704591797028502410516221241044213934812023000) * 10 ^ 70 +
        1792991335059353795605872183860166137793674776480533182242677294255785) * 10 ^ 70 +
        9861224603996412325790870185646760178788214895063793920780945557372906) * 10 ^ 70 +
        9070866227728621625548102384118993715111890761216422839784508683777876) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (287 - x)) = _
  rw [show 288 = 101 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_287_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (288 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_288 :
    recurrence4Scalar2Left.coeff 288 =
      (((((4627678912466691551614650 * 10 ^ 70 +
        9451273827582153507977622592993822812929007634214190151737173153941605) * 10 ^ 70 +
        9587725531271427939413154145246285664546357188520614792495457345543022) * 10 ^ 70 +
        9437348331119747547000658962197467000514218251696276557318660976307711) * 10 ^ 70 +
        2334816417035988440327847111560628472419351272931461553382809215509640) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (288 - x)) = _
  rw [show 289 = 102 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_288_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (289 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_289 :
    recurrence4Scalar2Left.coeff 289 =
      -(((((3149562183150964047365745 * 10 ^ 70 +
        7559551859646986601579344556403637957957382102033717008735846273367903) * 10 ^ 70 +
        5354227566694279186630714317103411141310187523717538488027977305785001) * 10 ^ 70 +
        2843621641774375677698031525905508653922100920792859295105069785742642) * 10 ^ 70 +
        5523249091985727284713729449188180224949041254506863442331487738991835) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (289 - x)) = _
  rw [show 290 = 103 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_289_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (290 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_290 :
    recurrence4Scalar2Left.coeff 290 =
      (((((2096791942489283004463699 * 10 ^ 70 +
        0325516038312708031438601707145585600335124118623300915663433336151614) * 10 ^ 70 +
        6003414768569847104913287855776935371886171217291904822369838904516931) * 10 ^ 70 +
        1287436787900103442884040709228357519849581179944874478350901342827539) * 10 ^ 70 +
        2904358553599015461845113912456274094401822939349135098941211679462493) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (290 - x)) = _
  rw [show 291 = 104 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_290_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (291 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_291 :
    recurrence4Scalar2Left.coeff 291 =
      -(((((1364906301720155408930823 * 10 ^ 70 +
        6131850846697172423659543111749319123324838457146576303314534574453182) * 10 ^ 70 +
        7924655666730675876711251986175964586426858295486857480753944815462815) * 10 ^ 70 +
        9477335259101705542977495198005440357640698531406095804761701830856831) * 10 ^ 70 +
        2410610329846305958518073349652827951221616458168471397959260650767506) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (291 - x)) = _
  rw [show 292 = 105 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_291_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (292 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_292 :
    recurrence4Scalar2Left.coeff 292 =
      (((((868127442104021087146706 * 10 ^ 70 +
        2433454664636871404597800396362113045466840631349354503144863706138859) * 10 ^ 70 +
        5443910638343289448398708337456810223369372941254595566526225632450233) * 10 ^ 70 +
        7483125263949639427285343804568468748633369356682566897859514239347637) * 10 ^ 70 +
        5200679545379955716879936411022474454571711515487992088727150273978375) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (292 - x)) = _
  rw [show 293 = 106 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_292_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (293 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_293 :
    recurrence4Scalar2Left.coeff 293 =
      -(((((538912927804086539361346 * 10 ^ 70 +
        6539535799061109648735063054911737561066571409890397238833948811691277) * 10 ^ 70 +
        1764926668853021256672635721124721665877374903855850897214758853090013) * 10 ^ 70 +
        9070273052686567589136762446611774593633323480327662595022434083121820) * 10 ^ 70 +
        3094845294976120781607063350574162102156273192910368327079859619719421) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (293 - x)) = _
  rw [show 294 = 107 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_293_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (294 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_294 :
    recurrence4Scalar2Left.coeff 294 =
      (((((325986818784689148834166 * 10 ^ 70 +
        6336995118105586620093679011331891677655255151719944143117586562947006) * 10 ^ 70 +
        0324388720510092745575640649121804572866567012328919186121866922478720) * 10 ^ 70 +
        7372524168295060810347451640560089623579743807303417088253650899756741) * 10 ^ 70 +
        3631234844978756765570158207304494310022024144068582888639420678710551) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (294 - x)) = _
  rw [show 295 = 108 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_294_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (295 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_295 :
    recurrence4Scalar2Left.coeff 295 =
      -(((((191685788399193860954925 * 10 ^ 70 +
        8260186508224139215689595439703771499192573215354062689557074279339836) * 10 ^ 70 +
        7133652426098199897820295687806354840897397748629794013480862090508651) * 10 ^ 70 +
        5313994010577681544808843469712843885502866724445239449730936520844077) * 10 ^ 70 +
        0830374460558141843322067496648341760839601075117903621120710493845985) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (295 - x)) = _
  rw [show 296 = 109 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_295_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (296 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_296 :
    recurrence4Scalar2Left.coeff 296 =
      (((((109181023445352652568367 * 10 ^ 70 +
        7833853927048573813399353120900766929587197911182991279346145334920634) * 10 ^ 70 +
        1631192125192162794692667484592618850537623518470796753946115769514575) * 10 ^ 70 +
        6295103749065342995385814563620557967500422672872723512263232599192598) * 10 ^ 70 +
        6261319181063324322101340835534657353943297905986241449798792520888076) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (296 - x)) = _
  rw [show 297 = 110 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_296_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (297 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_297 :
    recurrence4Scalar2Left.coeff 297 =
      -(((((59911430678852447535591 * 10 ^ 70 +
        4986582820558199165776576795835784749305092594384366809307819592212044) * 10 ^ 70 +
        9075523178587078880002309662239706562371835495897555707170501569175186) * 10 ^ 70 +
        3001175794915729512360986789011269566703852135710726480655421393503493) * 10 ^ 70 +
        9164402628721354452797179945630410660391550435226483595232512770607779) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (297 - x)) = _
  rw [show 298 = 111 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_297_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (298 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_298 :
    recurrence4Scalar2Left.coeff 298 =
      (((((31395143639587919169998 * 10 ^ 70 +
        6226573856306657217034897005733346868257346428822169686941898643561510) * 10 ^ 70 +
        8259411579572734411345929366825075922450266230672241456586195001228927) * 10 ^ 70 +
        9030512150710517197872754780232592231619447911039118367837475748110311) * 10 ^ 70 +
        5672917740159184414402368630748281492996146224170303516182565753139829) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (298 - x)) = _
  rw [show 299 = 112 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_298_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (299 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_299 :
    recurrence4Scalar2Left.coeff 299 =
      -(((((15471373763219108156584 * 10 ^ 70 +
        7413438412276954627474207889336571967386883632832094129874234021867990) * 10 ^ 70 +
        9542413411907297724316792384590613657584631212514687728579474795346028) * 10 ^ 70 +
        5455391339571399420553182026431431741557517891363756707091537176980638) * 10 ^ 70 +
        4330896995505001366738702681215988134272136234780122622419032951882785) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (299 - x)) = _
  rw [show 300 = 113 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_299_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (300 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_300 :
    recurrence4Scalar2Left.coeff 300 =
      (((((6954361776465469974883 * 10 ^ 70 +
        8957394516132967477334440869919878825993218377709587864311215394279373) * 10 ^ 70 +
        3419541200004444581642230268792693694568416332932847589949448309825417) * 10 ^ 70 +
        9851968083698251440267136152941268355655157389203233194277813335832086) * 10 ^ 70 +
        3830301679315512756200684494540007356272504173481860661674060143420216) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (300 - x)) = _
  rw [show 301 = 114 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_300_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (301 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_301 :
    recurrence4Scalar2Left.coeff 301 =
      -(((((2644589043091066295810 * 10 ^ 70 +
        5506259375334576732907437790900879421546326507814098133342277583197456) * 10 ^ 70 +
        9977399875452059872734514208667583012108430529594913712203235979730674) * 10 ^ 70 +
        4571382383754574092327941948826411423051026611897163424599079237453119) * 10 ^ 70 +
        8514102464296441746585005289544381238502166911661014996124099214642708) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (301 - x)) = _
  rw [show 302 = 115 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_301_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (302 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_302 :
    recurrence4Scalar2Left.coeff 302 =
      (((((628919473517694352708 * 10 ^ 70 +
        7252567958532875459109937279503131166418071484866372944841396680422732) * 10 ^ 70 +
        7598559198704692279476464991658479772927382201257167156250243173308198) * 10 ^ 70 +
        0861584065391238598512690712709545193535853222047979698418476469426434) * 10 ^ 70 +
        9588146953853424477248844642872559290187076936918680401762742686781354) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (302 - x)) = _
  rw [show 303 = 116 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_302_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (303 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_303 :
    recurrence4Scalar2Left.coeff 303 =
      (((((197920027697453469049 * 10 ^ 70 +
        0595746279261532835903996438082901316976146148845292153951652563351309) * 10 ^ 70 +
        7650807004517716831653626785817113226730519171132188408225786630388061) * 10 ^ 70 +
        4793538414797300941908901710418457967717481363726017466952792304600854) * 10 ^ 70 +
        4181814984116711499004198017542331220381171718075369582950282118847332) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (303 - x)) = _
  rw [show 304 = 117 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_303_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (304 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_304 :
    recurrence4Scalar2Left.coeff 304 =
      -(((((449847163978137945040 * 10 ^ 70 +
        2348888239973907699122142459546600603854772640606042140474673429607448) * 10 ^ 70 +
        7004804040368282366091355377646324532763141390715420570317054559781526) * 10 ^ 70 +
        5036946205653789358607305278615787310925950977613793409247920893861177) * 10 ^ 70 +
        4852994561066336382239114483247442768251291016440896954085300769394504) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (304 - x)) = _
  rw [show 305 = 118 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_304_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (305 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_305 :
    recurrence4Scalar2Left.coeff 305 =
      (((((452030430997925125313 * 10 ^ 70 +
        9408312501298418434985389958660466554854796235007382026428426997273345) * 10 ^ 70 +
        0585912769425348044708619128128088893931940636606508917183387693337751) * 10 ^ 70 +
        0732467546073203546166338190242703909227005590164535135793971378747917) * 10 ^ 70 +
        9538010622336683701500202573025296081676272480006991494938681828437996) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (305 - x)) = _
  rw [show 306 = 119 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_305_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (306 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_306 :
    recurrence4Scalar2Left.coeff 306 =
      -(((((366342023241722155451 * 10 ^ 70 +
        7536827472600665936472664083712029905599747608288656912413443241578371) * 10 ^ 70 +
        0850114488224966274305647360704118167705748582465349708024249376110958) * 10 ^ 70 +
        6157918308097508641501789998012420195322260803711949911919947655644703) * 10 ^ 70 +
        0104650308065349995775519555631381758238567053468079963223020293898017) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (306 - x)) = _
  rw [show 307 = 120 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_306_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (307 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_307 :
    recurrence4Scalar2Left.coeff 307 =
      (((((266375523252039165231 * 10 ^ 70 +
        9192717156759407170009351775810109086724707462780224019197190696431154) * 10 ^ 70 +
        5685940766391775521498199305445731013583363344437522599179503801861105) * 10 ^ 70 +
        5581918868488722510484088208719445795932323365301932340883644375730923) * 10 ^ 70 +
        3278069190731887104029085823159328633447112647827433678732502591798896) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (307 - x)) = _
  rw [show 308 = 121 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_307_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (308 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_308 :
    recurrence4Scalar2Left.coeff 308 =
      -(((((180632517451666025955 * 10 ^ 70 +
        1250821489586251807228360774176093759730497989260138880458955697653877) * 10 ^ 70 +
        3398955699447278818529494870714996317734357636232119339115894401827935) * 10 ^ 70 +
        8700739634081107836638630958516120874812966434661703451745422530509414) * 10 ^ 70 +
        4997919317345273339219312445322401793795972887825995772454324037246230) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (308 - x)) = _
  rw [show 309 = 122 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_308_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (309 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_309 :
    recurrence4Scalar2Left.coeff 309 =
      (((((116328627457166639097 * 10 ^ 70 +
        0153658566906454613033804242248135747667703047990121659866773141824728) * 10 ^ 70 +
        6700815587964083599829286654603187259454201694967958490319806829651797) * 10 ^ 70 +
        1781031987546811013367782297654219004690571466150799621204013694147374) * 10 ^ 70 +
        5749593500196626440231087366085353373092387087746497009717959548869896) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (309 - x)) = _
  rw [show 310 = 123 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_309_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (310 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_310 :
    recurrence4Scalar2Left.coeff 310 =
      -(((((71841194622788229037 * 10 ^ 70 +
        9908945347512429483967339075030329858507286027538769293369819704266870) * 10 ^ 70 +
        9781964220976761237997132879022368694162913766631753241176162574539205) * 10 ^ 70 +
        9809255350844252821926632345004800542074404925785109116626773484358886) * 10 ^ 70 +
        5440819375982269393055220243956806499397166735622254478856190013465460) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (310 - x)) = _
  rw [show 311 = 124 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_310_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (311 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_311 :
    recurrence4Scalar2Left.coeff 311 =
      (((((42776593745183289616 * 10 ^ 70 +
        4430880204248569536613503548070758822244907596741572542018018251984398) * 10 ^ 70 +
        2150930144625684043045161597118167962977534075851961470406991363339078) * 10 ^ 70 +
        9454756667791820967986391250870811801681960350764340412068057346246351) * 10 ^ 70 +
        0497733284411805842633925818600111941345632261624034484537299715968072) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (311 - x)) = _
  rw [show 312 = 125 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_311_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (312 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_312 :
    recurrence4Scalar2Left.coeff 312 =
      -(((((24628257652851383261 * 10 ^ 70 +
        4957094231686345775510588636306587981976498853655380807372231156979702) * 10 ^ 70 +
        4586561106430380964838389450687953782604440615914702780445513634002981) * 10 ^ 70 +
        9770037049444348154592393042171378307271767688445404265567029070084282) * 10 ^ 70 +
        2185094820066364130446041376284923467248989061405066453409048643032090) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (312 - x)) = _
  rw [show 313 = 126 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_312_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (313 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_313 :
    recurrence4Scalar2Left.coeff 313 =
      (((((13725648635079999449 * 10 ^ 70 +
        0563168933660779866110995819195894908401588497538415492093499575954322) * 10 ^ 70 +
        3202279417571739063423225796934363092935257075620332935493307987506495) * 10 ^ 70 +
        3140877389624718670865220451547277509000573119984246662737224093114888) * 10 ^ 70 +
        0933500681578889459824662072697858776908906723639340752807539421797202) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (313 - x)) = _
  rw [show 314 = 127 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_313_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (314 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_314 :
    recurrence4Scalar2Left.coeff 314 =
      -(((((7401475635705202073 * 10 ^ 70 +
        6690117946265726176780725075701772374315575171893374466752005768012495) * 10 ^ 70 +
        8605905850945204058368881644119058346229909259661889877034727546429199) * 10 ^ 70 +
        2293292293058017971365002262791179601046854815852788162614664717507741) * 10 ^ 70 +
        0639247756372819876199686553266155803305109267359176271139128803243982) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (314 - x)) = _
  rw [show 315 = 128 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_314_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (315 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_315 :
    recurrence4Scalar2Left.coeff 315 =
      (((((3853847905333722625 * 10 ^ 70 +
        2764913196275398078356848565566433025970426891494510874015696750343229) * 10 ^ 70 +
        5686138031303733913430334848762086922716702553979576060782466750949506) * 10 ^ 70 +
        0516210122879118547193433727860071569381387392678167074290495474148643) * 10 ^ 70 +
        5727186684891222220361285516424167123484743166557822486912014084824335) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (315 - x)) = _
  rw [show 316 = 129 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_315_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (316 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_316 :
    recurrence4Scalar2Left.coeff 316 =
      -(((((1929413465711199333 * 10 ^ 70 +
        3621125131855423663092828632710957334739088673673175711786586927137044) * 10 ^ 70 +
        9282103680979551757290871976279761618024962386491111072760347654546805) * 10 ^ 70 +
        7211514434961369426039127975170089373052133245296436192641497337734575) * 10 ^ 70 +
        9097217101874948097453543252609498052858647251357388903883748333655633) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (316 - x)) = _
  rw [show 317 = 130 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_316_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (317 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_317 :
    recurrence4Scalar2Left.coeff 317 =
      (((((921681333514914010 * 10 ^ 70 +
        7795541601940237542266506211981823776331961454186247888010967633305033) * 10 ^ 70 +
        6488417418037493613470931743491528949019538510314431320615998301471337) * 10 ^ 70 +
        0137731896080092882451715063683572695391019266969501742000586763406633) * 10 ^ 70 +
        4492408630278578152513803595983965480271772197345602424011849973225583) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (317 - x)) = _
  rw [show 318 = 131 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_317_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (318 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_318 :
    recurrence4Scalar2Left.coeff 318 =
      -(((((414235421643995258 * 10 ^ 70 +
        8541894287330860445385889509267055575735392744474021937057117591385880) * 10 ^ 70 +
        8253047767667301266470825497009318388301474373208643001713315737712940) * 10 ^ 70 +
        1422687296819835813358947028382729050356935755004753929219683691655431) * 10 ^ 70 +
        8653670368663043233834439980453942204645170284916799408189603020588980) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (318 - x)) = _
  rw [show 319 = 132 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_318_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (319 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_319 :
    recurrence4Scalar2Left.coeff 319 =
      (((((170261278033457092 * 10 ^ 70 +
        1099857883066357727050175477014097260877121003680631695554698885127247) * 10 ^ 70 +
        1778321803623990675998382813529589357824409003630798055293434880323669) * 10 ^ 70 +
        7098729699885462540688548912377765008260701638411672254102428785556348) * 10 ^ 70 +
        5811275985066209096716343621052189509012743381284758879811752910767610) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (319 - x)) = _
  rw [show 320 = 133 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_319_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (320 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_320 :
    recurrence4Scalar2Left.coeff 320 =
      -(((((59719236723639652 * 10 ^ 70 +
        6045469911206811790007724327173959338691377225911274630814364696135813) * 10 ^ 70 +
        5459575766537049173264421358843653370378780144346720270197775737217161) * 10 ^ 70 +
        5496149461867497115474248820785966106615726257341034908339418406968116) * 10 ^ 70 +
        7066636651611790467426025082470230186823544880808247289523153559745156) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (320 - x)) = _
  rw [show 321 = 134 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_320_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (321 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_321 :
    recurrence4Scalar2Left.coeff 321 =
      (((((13731658550403596 * 10 ^ 70 +
        1623566598299734327025662043276057267875594586584219396726004357075128) * 10 ^ 70 +
        3744909936421407270064034615354289018366897555732040345712845698099433) * 10 ^ 70 +
        4222919667323681339389382908574878264710652954630861390768996435785417) * 10 ^ 70 +
        7690515131790892863945205358968481767563820168572106675699918698459763) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (321 - x)) = _
  rw [show 322 = 135 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_321_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (322 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_322 :
    recurrence4Scalar2Left.coeff 322 =
      (((((2781463830516638 * 10 ^ 70 +
        8007529238072184437340557340018958950190893541023110181278916477683826) * 10 ^ 70 +
        9909937746131207188559878528028918193141229397438752224882340855056114) * 10 ^ 70 +
        7752612514618724631232608265324153450398347178716549908488545390344759) * 10 ^ 70 +
        5728330138010157514599056874412916464920089580732135991212850253881690) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (322 - x)) = _
  rw [show 323 = 136 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_322_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (323 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_323 :
    recurrence4Scalar2Left.coeff 323 =
      -(((((6895092946533194 * 10 ^ 70 +
        3809345686930751750279375215753460318862407330734890435365656847622347) * 10 ^ 70 +
        2356777206527911720136370192307456008270429562981081234471909406439640) * 10 ^ 70 +
        7161167828929570540902295012325259258097962272846294423909597129523906) * 10 ^ 70 +
        9483537111401366144416295017705739845692303145657661116097739680999407) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (323 - x)) = _
  rw [show 324 = 137 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_323_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (324 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_324 :
    recurrence4Scalar2Left.coeff 324 =
      (((((6462515006980644 * 10 ^ 70 +
        3067020380101922044495300481992197258892557740151177629747425882805594) * 10 ^ 70 +
        3354660659962689516928771579087643980674058423575850309655331528012826) * 10 ^ 70 +
        4629547656404936049148812322481841862189798057812237976250599516976803) * 10 ^ 70 +
        4499941886124109861300599741461417116180489597071184585356807537439855) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (324 - x)) = _
  rw [show 325 = 138 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_324_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (325 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_325 :
    recurrence4Scalar2Left.coeff 325 =
      -(((((4821844661162257 * 10 ^ 70 +
        3092916591313185973334737086855769294431988009001279174088345235861443) * 10 ^ 70 +
        7952699953258668386040349985063039585103687688526467057524342291463750) * 10 ^ 70 +
        3812883666634081656344918051426848679944180322562543707046996104749362) * 10 ^ 70 +
        9705299135653696830245964274982077235434240135497363146606644442994177) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (325 - x)) = _
  rw [show 326 = 139 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_325_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (326 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_326 :
    recurrence4Scalar2Left.coeff 326 =
      (((((3220024611122469 * 10 ^ 70 +
        2558198070965847033580564480658618939177498100861986320871662536581978) * 10 ^ 70 +
        9641708347619297048246667313097787341841788334041272773586564374932783) * 10 ^ 70 +
        2449071055229786524724160821161280738731156247841498185155521979527313) * 10 ^ 70 +
        1048839724794446753301093312972540147856348931360822846872175548114696) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (326 - x)) = _
  rw [show 327 = 140 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_326_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (327 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_327 :
    recurrence4Scalar2Left.coeff 327 =
      -(((((2006534518331477 * 10 ^ 70 +
        0483660377014665984775318132094625850572213122577083837448693308269366) * 10 ^ 70 +
        5735834838786295907107845857422950196435521586279276085657450318212796) * 10 ^ 70 +
        9599296324134578911924278522508756760093418848607807804994312315746371) * 10 ^ 70 +
        1672811278403747033319576318995122778752864030764124835577633575128714) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (327 - x)) = _
  rw [show 328 = 141 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_327_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (328 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_328 :
    recurrence4Scalar2Left.coeff 328 =
      (((((1189939219579801 * 10 ^ 70 +
        4166253197303509941369321489086083181281116918788351559567588153174889) * 10 ^ 70 +
        8607990611038528211727369227132969008100401832501186550463706811601768) * 10 ^ 70 +
        8055654944865951286118938381611510084781626062898200316148435518302916) * 10 ^ 70 +
        5625522005484168906651370959120528433024203255347666041969128386670630) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (328 - x)) = _
  rw [show 329 = 142 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_328_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (329 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_329 :
    recurrence4Scalar2Left.coeff 329 =
      -(((((678893015756049 * 10 ^ 70 +
        9445929361913897349887822930082310900561401777213368656504210089464361) * 10 ^ 70 +
        9338323428057962912455720991016595710561528628687493461963274651689560) * 10 ^ 70 +
        4758176616335890785629085900845704296055711123179009740341757678964142) * 10 ^ 70 +
        1422253444768906755241364906034797738023448222899693902049066268446377) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (329 - x)) = _
  rw [show 330 = 143 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (330 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_330 :
    recurrence4Scalar2Left.coeff 330 =
      (((((375086688677044 * 10 ^ 70 +
        4538415979987056457833288285701525395662310455897625086663632498309314) * 10 ^ 70 +
        1604205892170079684023715698545573682240942821253854606796855828609348) * 10 ^ 70 +
        5685022757592599992133623265098000138553894646995787197624290030543180) * 10 ^ 70 +
        7640840320159201377272550798819285078129687956530153712198299030670164) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (330 - x)) = _
  rw [show 331 = 144 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 25 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (331 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_331 :
    recurrence4Scalar2Left.coeff 331 =
      -(((((201540884321432 * 10 ^ 70 +
        9546426934900109995113466714688280973113723499488409150850728132221802) * 10 ^ 70 +
        9221556589630816736910500599363794094603801468455901192997491697637824) * 10 ^ 70 +
        3644570586011830922725721835710606473905723023032945706298042990815933) * 10 ^ 70 +
        5526977054644241163747897116332943118839836417861934025057472155477173) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (331 - x)) = _
  rw [show 332 = 145 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 24 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (332 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_332 :
    recurrence4Scalar2Left.coeff 332 =
      (((((105619655507277 * 10 ^ 70 +
        7712398148487273366906987831015228534095358722317299680244404346113868) * 10 ^ 70 +
        2236677488413415078470013796637750065224728124825297216924751636082847) * 10 ^ 70 +
        4511636073922705549326067823899658430258178332121017560894729163332985) * 10 ^ 70 +
        1782096702239196488875744865788220676375375790933173737267830506659388) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (332 - x)) = _
  rw [show 333 = 146 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 23 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (333 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_333 :
    recurrence4Scalar2Left.coeff 333 =
      -(((((54093486270793 * 10 ^ 70 +
        5320816745962935107421490628155423227008198726028335475505864451075979) * 10 ^ 70 +
        8227275512521273591728975858471820966773416743724167063603532920292537) * 10 ^ 70 +
        4737109901167315649283376742179363742133511767996070414499508522628986) * 10 ^ 70 +
        7757898603563514869219208937745278932050384936277062527604954811467233) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (333 - x)) = _
  rw [show 334 = 147 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 22 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (334 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_334 :
    recurrence4Scalar2Left.coeff 334 =
      (((((27112973328850 * 10 ^ 70 +
        9393465969010054720519690632874904115982116552825088296990960630590850) * 10 ^ 70 +
        8614106886881783312674325427593031671842123050103478019672986408075390) * 10 ^ 70 +
        5354345298184380839063926874880245860872118479720988557776923081308738) * 10 ^ 70 +
        0498398703850403990870575239115203919647644612894445909073694624931997) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (334 - x)) = _
  rw [show 335 = 148 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 21 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (335 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_335 :
    recurrence4Scalar2Left.coeff 335 =
      -(((((13312976636055 * 10 ^ 70 +
        1383070376206978873340508502053416144112594782401001072960547006411768) * 10 ^ 70 +
        7015203199698212956378007221328775773486109353459902167917789308474600) * 10 ^ 70 +
        4686372147786985905476104170936987005254775462454320096327323326474905) * 10 ^ 70 +
        0987890149314219013960494070288540824321059208706041120448003169860329) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (335 - x)) = _
  rw [show 336 = 149 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 20 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (336 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_336 :
    recurrence4Scalar2Left.coeff 336 =
      (((((6408282371031 * 10 ^ 70 +
        1679994875131778697043300000092410476145890671232913018511949304407132) * 10 ^ 70 +
        0420000815335273398832176800417078340515761058765681970598653736101952) * 10 ^ 70 +
        5343871460683644016905011714749205247757510300857236165143193689446177) * 10 ^ 70 +
        9772059908840729614477399837975948379795029055751548345350669608616400) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (336 - x)) = _
  rw [show 337 = 150 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 19 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (337 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_337 :
    recurrence4Scalar2Left.coeff 337 =
      -(((((3025377227428 * 10 ^ 70 +
        4002693384943092014017261277828614795593834106084714087866231847874290) * 10 ^ 70 +
        3958155183355723297172264710024022036502042152487497260241023102172540) * 10 ^ 70 +
        1157582921007774048923007631788247317277993331244150265985895100269226) * 10 ^ 70 +
        8897927896292563699726493623345500805884325614313630234079340969676295) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (337 - x)) = _
  rw [show 338 = 151 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 18 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (338 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_338 :
    recurrence4Scalar2Left.coeff 338 =
      (((((1401243942903 * 10 ^ 70 +
        0939043520248288901057472037487285369773051254991943156014923648763916) * 10 ^ 70 +
        7791139320957395705153975636557693603937888852188692160208052318408626) * 10 ^ 70 +
        2290823782144382964047399087192944271849723054005939214633060127529278) * 10 ^ 70 +
        1754083412979466616914990112406231100903198547807427270844422432821703) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (338 - x)) = _
  rw [show 339 = 152 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 17 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (339 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_339 :
    recurrence4Scalar2Left.coeff 339 =
      -(((((636804671152 * 10 ^ 70 +
        4938269744116422570501772839127364124384698075621053715503732689916815) * 10 ^ 70 +
        1426149208759214689601107594164926544085874153298586594223694250092822) * 10 ^ 70 +
        0255387208651440170621818923101640614707344947652926350936178074535044) * 10 ^ 70 +
        7957791633332051067822994856809641826912764384387703487369413460241226) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (339 - x)) = _
  rw [show 340 = 153 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 16 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (340 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_340 :
    recurrence4Scalar2Left.coeff 340 =
      (((((283966503762 * 10 ^ 70 +
        6290132853809612198113940948401319771511362215266946355332327830678981) * 10 ^ 70 +
        2737014787048888963910826054826563928668987630057550320919338578181635) * 10 ^ 70 +
        9476004950047455070591860139332312341334991725038711705004245073189962) * 10 ^ 70 +
        0074503805428525522621867116267393250311952360679735579388592993571055) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (340 - x)) = _
  rw [show 341 = 154 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 15 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (341 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_341 :
    recurrence4Scalar2Left.coeff 341 =
      -(((((124240537690 * 10 ^ 70 +
        6189100171817612027288208633898072753822473372491381941993195743740856) * 10 ^ 70 +
        3883959151162086582857168523978468479083449145193053884196904897297249) * 10 ^ 70 +
        1075592255139258768098191443008982666416615079416698258112588833541187) * 10 ^ 70 +
        7170703774702630636633439732481054234692138626587266083222158011144956) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (341 - x)) = _
  rw [show 342 = 155 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 14 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (342 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_342 :
    recurrence4Scalar2Left.coeff 342 =
      (((((53324443839 * 10 ^ 70 +
        9654519803140177428660819035842465630073247100728642143593208089223549) * 10 ^ 70 +
        7321891191996910525908228997066312459195490171702191888500710134266121) * 10 ^ 70 +
        0446251683306979432165042492230724942500691714498142819954254831813391) * 10 ^ 70 +
        3187517085866169886667542568436265923537429279155125422706284576410277) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (342 - x)) = _
  rw [show 343 = 156 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 13 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (343 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_343 :
    recurrence4Scalar2Left.coeff 343 =
      -(((((22447096105 * 10 ^ 70 +
        4173403219049989406821795092347018547469803340800462063173826334269705) * 10 ^ 70 +
        4489459484703171616845856966770324102472792170965348832619888902751503) * 10 ^ 70 +
        2126495102209779264742228108151421017516123759329033677983772119936544) * 10 ^ 70 +
        0124895327721360966286504051691956078661255393206780553195698852661727) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (343 - x)) = _
  rw [show 344 = 157 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 12 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (344 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_344 :
    recurrence4Scalar2Left.coeff 344 =
      (((((9265129258 * 10 ^ 70 +
        3078050725348679442793013312330004427366538106340053781727559648577816) * 10 ^ 70 +
        7153933818295117347298352276377988322601749988260508777513136354925177) * 10 ^ 70 +
        4564275718995328281332209079938326738509736950250160120668930057773901) * 10 ^ 70 +
        2598282314971090156598800127337711462807655972414364785565276692739596) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (344 - x)) = _
  rw [show 345 = 158 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 11 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (345 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_345 :
    recurrence4Scalar2Left.coeff 345 =
      -(((((3748730941 * 10 ^ 70 +
        8432343222047562957413145164089393345266687351248453703831270662283985) * 10 ^ 70 +
        9351755756188284761082451270906961966057676109932575013257290075886581) * 10 ^ 70 +
        5876519454433020883029336929911860045369351371609255384731861210049955) * 10 ^ 70 +
        4814739840971570171497147200459004617856283595787314512808037249487768) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (345 - x)) = _
  rw [show 346 = 159 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 10 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (346 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_346 :
    recurrence4Scalar2Left.coeff 346 =
      (((((1486493110 * 10 ^ 70 +
        3341881751618371627058571776936832328027671805780828384486939947887180) * 10 ^ 70 +
        0737380226235401795828094471344289899890792636772562163146052037693391) * 10 ^ 70 +
        8485236910772137837349382476641268889895594055309067525623001143680386) * 10 ^ 70 +
        6317798596061592589909546910907448672333073838096856790240198679254674) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (346 - x)) = _
  rw [show 347 = 160 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 9 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (347 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (347 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_347 :
    recurrence4Scalar2Left.coeff 347 =
      -(((((577629882 * 10 ^ 70 +
        7505080338029484325971177788571092964552504004307152081098885365118785) * 10 ^ 70 +
        7484438121448120687280262668424320691183470104528837107401922099720727) * 10 ^ 70 +
        7226287834955454757638270803793996169445584600822309578864781016380776) * 10 ^ 70 +
        1545887652805606967887279212277529761329936063020227639695353450168784) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (347 - x)) = _
  rw [show 348 = 161 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 8 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (348 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (348 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_348 :
    recurrence4Scalar2Left.coeff 348 =
      (((((220001814 * 10 ^ 70 +
        8423552410939914434720805988015274154007670099865991412755388001310634) * 10 ^ 70 +
        9160869155491427295446503690654590815211849397233115734852510886662793) * 10 ^ 70 +
        1233590698350485177865252255693944546384851248144431931259819743015979) * 10 ^ 70 +
        3913688710854872679818164756929748370892269210518220018852825368688894) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (348 - x)) = _
  rw [show 349 = 162 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 7 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (349 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (349 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_349 :
    recurrence4Scalar2Left.coeff 349 =
      -(((((82185261 * 10 ^ 70 +
        1786113160217194807086245129327430599646594784714394966165848087728468) * 10 ^ 70 +
        9387032127093268685062318528936667537664179451933888973627592253156161) * 10 ^ 70 +
        1050058523278258794421352429858928297600160938022746942955318458100346) * 10 ^ 70 +
        5121533017067906696512467865706158813529412457679260873913314914091940) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (349 - x)) = _
  rw [show 350 = 163 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 6 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (350 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (350 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_350 :
    recurrence4Scalar2Left.coeff 350 =
      (((((30160028 * 10 ^ 70 +
        0110100259506704056420203631476224549793145079765364712484391401929491) * 10 ^ 70 +
        0183100612481195177647315255485479159214642090092504012570044537318262) * 10 ^ 70 +
        7675612686397957204737461340871056532845827357131454232505404130682624) * 10 ^ 70 +
        7069712607085021088190226780501945661866642748750366483812630871018607) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (350 - x)) = _
  rw [show 351 = 164 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 5 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (351 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (351 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_351 :
    recurrence4Scalar2Left.coeff 351 =
      -(((((10905230 * 10 ^ 70 +
        5840228171600525116737087970702732099011239515385497063450718454339670) * 10 ^ 70 +
        5203038783049478316695849612926146772661192494855478607043713907964008) * 10 ^ 70 +
        0842396024592200296121163181608039176815124836122271956584372833285745) * 10 ^ 70 +
        2728447968531631387165465428966023299650313074155404068704396412222919) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (351 - x)) = _
  rw [show 352 = 165 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 4 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (352 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (352 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_352 :
    recurrence4Scalar2Left.coeff 352 =
      (((((3905159 * 10 ^ 70 +
        7070905608218817969033090792020030154350902904091095663921481148817136) * 10 ^ 70 +
        6872763262962305562698504113688809216999860635731816510522134393636422) * 10 ^ 70 +
        8072992288259923863185732606455459247619003566934462664010112531423964) * 10 ^ 70 +
        9630623312353118993807071664454047751285270777352281155106890698342090) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (352 - x)) = _
  rw [show 353 = 166 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 3 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (353 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (353 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_353 :
    recurrence4Scalar2Left.coeff 353 =
      -(((((1396283 * 10 ^ 70 +
        0271879310743719198251818049117684989404374284616940794411008128554270) * 10 ^ 70 +
        3271651779365645382382405603630644578225449885934204375714342081079774) * 10 ^ 70 +
        4090619526741127609189373004722991468223476133169761879877618356266945) * 10 ^ 70 +
        9395248521450016591611424514021057636880252575790347530480039885542043) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (353 - x)) = _
  rw [show 354 = 167 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 2 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (354 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (354 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_354 :
    recurrence4Scalar2Left.coeff 354 =
      (((((504246 * 10 ^ 70 +
        7317273458876157020520556050005707856640926130642829771028329081029119) * 10 ^ 70 +
        4178639102847890857122526109595010433162558491302639957845809644478111) * 10 ^ 70 +
        3397484913099721418116055413139116636160674585523824922776040059408908) * 10 ^ 70 +
        3073535489207567612901652612960619271958617142929959768600867992308131) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (354 - x)) = _
  rw [show 355 = 168 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 1 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (355 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (355 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_355 :
    recurrence4Scalar2Left.coeff 355 =
      -(((((186518 * 10 ^ 70 +
        3156559646584933794910129725356622288784599201893043195878648484165500) * 10 ^ 70 +
        7874005882915842266240046779371138274502764538075700204802116502313626) * 10 ^ 70 +
        8723429632691950366829893457656406174120329514139865170891215718865222) * 10 ^ 70 +
        3166067879171752179156947076086666890689160365729804553643637141681010) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (355 - x)) = _
  rw [show 356 = 169 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (356 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (356 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_356 :
    recurrence4Scalar2Left.coeff 356 =
      (((((71605 * 10 ^ 70 +
        7633007975110929685706068875225532967090388733873083937800849496514619) * 10 ^ 70 +
        7261964336461204320749415172608805749877564311795546344849070291563920) * 10 ^ 70 +
        2907755376920668468007657982897117517520248687837675559193316102607610) * 10 ^ 70 +
        9053159087383177102787406143299926752464674128260583103663439191588388) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (356 - x)) = _
  rw [show 357 = 170 +
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
    rw [show 59 = 31 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (357 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (357 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_357 :
    recurrence4Scalar2Left.coeff 357 =
      -(((((28745 * 10 ^ 70 +
        4042907234695573924564802315134243093292486379658467657034920878072168) * 10 ^ 70 +
        3226260429897622076916597873452397718351396511280582398543094964839949) * 10 ^ 70 +
        2105107547427736187909509587241796467411429260104085020786214180262098) * 10 ^ 70 +
        8781577620024539431487967425163914546017745945196113871546666660775406) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (357 - x)) = _
  rw [show 358 = 171 +
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
    rw [show 59 = 30 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
