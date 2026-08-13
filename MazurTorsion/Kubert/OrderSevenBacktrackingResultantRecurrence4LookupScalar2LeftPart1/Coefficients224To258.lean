/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
