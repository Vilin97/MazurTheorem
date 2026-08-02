/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A1_coeff_1
  recurrence4A1_coeff_10
  recurrence4A1_coeff_100
  recurrence4A1_coeff_101
  recurrence4A1_coeff_102
  recurrence4A1_coeff_103
  recurrence4A1_coeff_104
  recurrence4A1_coeff_105
  recurrence4A1_coeff_106
  recurrence4A1_coeff_107
  recurrence4A1_coeff_108
  recurrence4A1_coeff_109
  recurrence4A1_coeff_11
  recurrence4A1_coeff_110
  recurrence4A1_coeff_111
  recurrence4A1_coeff_112
  recurrence4A1_coeff_113
  recurrence4A1_coeff_114
  recurrence4A1_coeff_115
  recurrence4A1_coeff_116
  recurrence4A1_coeff_117
  recurrence4A1_coeff_118
  recurrence4A1_coeff_119
  recurrence4A1_coeff_12
  recurrence4A1_coeff_120
  recurrence4A1_coeff_121
  recurrence4A1_coeff_122
  recurrence4A1_coeff_123
  recurrence4A1_coeff_124
  recurrence4A1_coeff_125
  recurrence4A1_coeff_126
  recurrence4A1_coeff_127
  recurrence4A1_coeff_128
  recurrence4A1_coeff_129
  recurrence4A1_coeff_13
  recurrence4A1_coeff_130
  recurrence4A1_coeff_131
  recurrence4A1_coeff_132
  recurrence4A1_coeff_133
  recurrence4A1_coeff_134
  recurrence4A1_coeff_135
  recurrence4A1_coeff_136
  recurrence4A1_coeff_137
  recurrence4A1_coeff_138
  recurrence4A1_coeff_139
  recurrence4A1_coeff_14
  recurrence4A1_coeff_140
  recurrence4A1_coeff_141
  recurrence4A1_coeff_142
  recurrence4A1_coeff_143
  recurrence4A1_coeff_144
  recurrence4A1_coeff_145
  recurrence4A1_coeff_146
  recurrence4A1_coeff_147
  recurrence4A1_coeff_148
  recurrence4A1_coeff_149
  recurrence4A1_coeff_15
  recurrence4A1_coeff_150
  recurrence4A1_coeff_151
  recurrence4A1_coeff_152
  recurrence4A1_coeff_153
  recurrence4A1_coeff_154
  recurrence4A1_coeff_155
  recurrence4A1_coeff_156

attribute [local simp]
  recurrence4A1_coeff_157
  recurrence4A1_coeff_158
  recurrence4A1_coeff_159
  recurrence4A1_coeff_16
  recurrence4A1_coeff_160
  recurrence4A1_coeff_161
  recurrence4A1_coeff_162
  recurrence4A1_coeff_163
  recurrence4A1_coeff_164
  recurrence4A1_coeff_165
  recurrence4A1_coeff_166
  recurrence4A1_coeff_167
  recurrence4A1_coeff_168
  recurrence4A1_coeff_169
  recurrence4A1_coeff_17
  recurrence4A1_coeff_170
  recurrence4A1_coeff_171
  recurrence4A1_coeff_172
  recurrence4A1_coeff_173
  recurrence4A1_coeff_174
  recurrence4A1_coeff_175
  recurrence4A1_coeff_176
  recurrence4A1_coeff_177
  recurrence4A1_coeff_178
  recurrence4A1_coeff_179
  recurrence4A1_coeff_18
  recurrence4A1_coeff_180
  recurrence4A1_coeff_181
  recurrence4A1_coeff_182
  recurrence4A1_coeff_183
  recurrence4A1_coeff_184
  recurrence4A1_coeff_185
  recurrence4A1_coeff_186
  recurrence4A1_coeff_187
  recurrence4A1_coeff_188
  recurrence4A1_coeff_189
  recurrence4A1_coeff_19
  recurrence4A1_coeff_190
  recurrence4A1_coeff_2
  recurrence4A1_coeff_20
  recurrence4A1_coeff_21
  recurrence4A1_coeff_22
  recurrence4A1_coeff_23
  recurrence4A1_coeff_24
  recurrence4A1_coeff_25
  recurrence4A1_coeff_26
  recurrence4A1_coeff_27
  recurrence4A1_coeff_28
  recurrence4A1_coeff_29
  recurrence4A1_coeff_3
  recurrence4A1_coeff_30
  recurrence4A1_coeff_31
  recurrence4A1_coeff_32
  recurrence4A1_coeff_33
  recurrence4A1_coeff_34
  recurrence4A1_coeff_35
  recurrence4A1_coeff_36
  recurrence4A1_coeff_37
  recurrence4A1_coeff_38
  recurrence4A1_coeff_39
  recurrence4A1_coeff_4
  recurrence4A1_coeff_40
  recurrence4A1_coeff_41
  recurrence4A1_coeff_42

attribute [local simp]
  recurrence4A1_coeff_43
  recurrence4A1_coeff_44
  recurrence4A1_coeff_45
  recurrence4A1_coeff_46
  recurrence4A1_coeff_47
  recurrence4A1_coeff_48
  recurrence4A1_coeff_49
  recurrence4A1_coeff_5
  recurrence4A1_coeff_50
  recurrence4A1_coeff_51
  recurrence4A1_coeff_52
  recurrence4A1_coeff_53
  recurrence4A1_coeff_54
  recurrence4A1_coeff_55
  recurrence4A1_coeff_56
  recurrence4A1_coeff_57
  recurrence4A1_coeff_58
  recurrence4A1_coeff_59
  recurrence4A1_coeff_6
  recurrence4A1_coeff_60
  recurrence4A1_coeff_61
  recurrence4A1_coeff_62
  recurrence4A1_coeff_63
  recurrence4A1_coeff_64
  recurrence4A1_coeff_65
  recurrence4A1_coeff_66
  recurrence4A1_coeff_67
  recurrence4A1_coeff_68
  recurrence4A1_coeff_69
  recurrence4A1_coeff_7
  recurrence4A1_coeff_70
  recurrence4A1_coeff_71
  recurrence4A1_coeff_72
  recurrence4A1_coeff_73
  recurrence4A1_coeff_74
  recurrence4A1_coeff_75
  recurrence4A1_coeff_76
  recurrence4A1_coeff_77
  recurrence4A1_coeff_78
  recurrence4A1_coeff_79
  recurrence4A1_coeff_8
  recurrence4A1_coeff_80
  recurrence4A1_coeff_81
  recurrence4A1_coeff_82
  recurrence4A1_coeff_83
  recurrence4A1_coeff_84
  recurrence4A1_coeff_85
  recurrence4A1_coeff_86
  recurrence4A1_coeff_87
  recurrence4A1_coeff_88
  recurrence4A1_coeff_89
  recurrence4A1_coeff_9
  recurrence4A1_coeff_90
  recurrence4A1_coeff_91
  recurrence4A1_coeff_92
  recurrence4A1_coeff_93
  recurrence4A1_coeff_94
  recurrence4A1_coeff_95
  recurrence4A1_coeff_96
  recurrence4A1_coeff_97
  recurrence4A1_coeff_98
  recurrence4A1_coeff_99
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101

attribute [local simp]
  recurrence4LeadingSquare_coeff_102
  recurrence4LeadingSquare_coeff_103
  recurrence4LeadingSquare_coeff_104
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_166
  recurrence4LeadingSquare_coeff_167
  recurrence4LeadingSquare_coeff_168
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_230
  recurrence4LeadingSquare_coeff_231
  recurrence4LeadingSquare_coeff_232
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_294
  recurrence4LeadingSquare_coeff_295
  recurrence4LeadingSquare_coeff_296
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

private theorem recurrence4Scalar1Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (272 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (272 + x) *
        remainder4Coefficient1.coeff (272 - (272 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 272 + x
  · rw [recurrence4LeadingSquare_coeff_high (272 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (272 - (272 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_272 :
    recurrence4Scalar1Left.coeff 272 =
      -(((((315611412980693173253623342 * 10 ^ 70 +
        3677886585848540737571302022342927831942415912291118254822172897471716) * 10 ^ 70 +
        2255264827129675610615547639116544489102298901086671568538476675824865) * 10 ^ 70 +
        5507307596256309180569371995149839538972363677412311736827800187271953) * 10 ^ 70 +
        8379152312811953192414707885914092653858862616010204143907909018476983) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (272 - x)) = _
  rw [show 273 = 82 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (273 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (273 + x) *
        remainder4Coefficient1.coeff (273 - (273 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 273 + x
  · rw [recurrence4LeadingSquare_coeff_high (273 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (273 - (273 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_273 :
    recurrence4Scalar1Left.coeff 273 =
      (((((101510129026410362502831230 * 10 ^ 70 +
        9706300648154400526925225748683836966463329145682637454911170478692397) * 10 ^ 70 +
        9774280448914728250222039465090636104531792919380382891082161311616709) * 10 ^ 70 +
        1433559047843205419918111730691252715057893845941132897795730470751862) * 10 ^ 70 +
        7180329063418116426918719352693306146589219858784819477796940026882909) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (273 - x)) = _
  rw [show 274 = 83 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (274 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (274 + x) *
        remainder4Coefficient1.coeff (274 - (274 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 274 + x
  · rw [recurrence4LeadingSquare_coeff_high (274 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (274 - (274 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_274 :
    recurrence4Scalar1Left.coeff 274 =
      (((((55918795499793013055294467 * 10 ^ 70 +
        4095616979264414873817081283436790653359041789933741370401338480172791) * 10 ^ 70 +
        4054931617971638818053242137155265071983436855300207382503360895057068) * 10 ^ 70 +
        6617064066200120452579898256196769351361955607688991165221157988947498) * 10 ^ 70 +
        1596727065812987240576694085871276433976078156535235298292118610463914) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (274 - x)) = _
  rw [show 275 = 84 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (275 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (275 + x) *
        remainder4Coefficient1.coeff (275 - (275 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 275 + x
  · rw [recurrence4LeadingSquare_coeff_high (275 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (275 - (275 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_275 :
    recurrence4Scalar1Left.coeff 275 =
      -(((((162619189816013407984776318 * 10 ^ 70 +
        6580037110647146585735110578066582837889169687494833909205009319048027) * 10 ^ 70 +
        4901139951210068889976499878271908187468170502207205710180441108930265) * 10 ^ 70 +
        7853540618352927123852030693773106630260754088309101874986778479697160) * 10 ^ 70 +
        0166195803366141162138758973396006614474692791292487219947273273736774) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (275 - x)) = _
  rw [show 276 = 85 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (276 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (276 + x) *
        remainder4Coefficient1.coeff (276 - (276 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 276 + x
  · rw [recurrence4LeadingSquare_coeff_high (276 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (276 - (276 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_276 :
    recurrence4Scalar1Left.coeff 276 =
      (((((226469457627986724776483980 * 10 ^ 70 +
        5823436466162492327572981492504362832286135359302436204604518485257365) * 10 ^ 70 +
        5080320311826310973430219034850923226520731546921364038556336366224482) * 10 ^ 70 +
        9844244377190040256543017756763145947288896695499371140940324195899966) * 10 ^ 70 +
        1325006772572947364039978989211002502589174221644134354361113117993475) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (276 - x)) = _
  rw [show 277 = 86 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (277 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (277 + x) *
        remainder4Coefficient1.coeff (277 - (277 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 277 + x
  · rw [recurrence4LeadingSquare_coeff_high (277 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (277 - (277 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_277 :
    recurrence4Scalar1Left.coeff 277 =
      -(((((256163914753118703613974707 * 10 ^ 70 +
        6367630819891853890046801304914041873726688975659788809953318164858974) * 10 ^ 70 +
        5360909874851584961194852333452101360809467564168443151176330334953192) * 10 ^ 70 +
        2723422253167805189815984531970325321390182159875148953279987918681779) * 10 ^ 70 +
        5358338174475390874400112366359731107287475469109719867419167318343108) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (277 - x)) = _
  rw [show 278 = 87 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (278 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (278 + x) *
        remainder4Coefficient1.coeff (278 - (278 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 278 + x
  · rw [recurrence4LeadingSquare_coeff_high (278 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (278 - (278 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_278 :
    recurrence4Scalar1Left.coeff 278 =
      (((((260309251708460426609577919 * 10 ^ 70 +
        4945733928761377808903688732385671746389537811363181367492914767087885) * 10 ^ 70 +
        6061176397329978836166875967747588965132738653793630130396539005964456) * 10 ^ 70 +
        6264537932586340419089070403822587136525305254141463373062056368608477) * 10 ^ 70 +
        8124819871084314589709211813888730095282750753248730138426036652543960) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (278 - x)) = _
  rw [show 279 = 88 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (279 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (279 + x) *
        remainder4Coefficient1.coeff (279 - (279 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 279 + x
  · rw [recurrence4LeadingSquare_coeff_high (279 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (279 - (279 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_279 :
    recurrence4Scalar1Left.coeff 279 =
      -(((((246769663117543132249781349 * 10 ^ 70 +
        7797751850468418026891511350596993647432842880983791981810229452218586) * 10 ^ 70 +
        5430131333035836353128921588154027975945163622528837726673825711889498) * 10 ^ 70 +
        8797937173614797175755659818912135576722052091572465792144102510683130) * 10 ^ 70 +
        6691212993622369377680498343758495241952920921212268965160994087627122) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (279 - x)) = _
  rw [show 280 = 89 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (280 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (280 + x) *
        remainder4Coefficient1.coeff (280 - (280 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 280 + x
  · rw [recurrence4LeadingSquare_coeff_high (280 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (280 - (280 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_280 :
    recurrence4Scalar1Left.coeff 280 =
      (((((222258815103733556245848997 * 10 ^ 70 +
        4498441190350374674719534776626961515661100789503810647273154849795496) * 10 ^ 70 +
        9247566342534508269072147923461170290181991414266848856801475464922577) * 10 ^ 70 +
        7120802872314360932613112798088779087570451963694525993698016387129519) * 10 ^ 70 +
        1069958882557858939593593544351564160998533288164078811664756789404234) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (280 - x)) = _
  rw [show 281 = 90 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (281 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (281 + x) *
        remainder4Coefficient1.coeff (281 - (281 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 281 + x
  · rw [recurrence4LeadingSquare_coeff_high (281 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (281 - (281 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_281 :
    recurrence4Scalar1Left.coeff 281 =
      -(((((192150671437389011715398357 * 10 ^ 70 +
        6639715803981022829969151243647485838014048632163533271634551677787607) * 10 ^ 70 +
        7096638363136162432698609847322172864792535125819856885137866745768733) * 10 ^ 70 +
        3744616590358518664477183601764357667073656042542371188235027456379587) * 10 ^ 70 +
        6985145439771077847291572759979039191928050390596849941755984349943906) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (281 - x)) = _
  rw [show 282 = 91 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (282 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (282 + x) *
        remainder4Coefficient1.coeff (282 - (282 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 282 + x
  · rw [recurrence4LeadingSquare_coeff_high (282 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (282 - (282 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_282 :
    recurrence4Scalar1Left.coeff 282 =
      (((((160465281340788036931006122 * 10 ^ 70 +
        1645660959883232132804802113665719687434276013821675443156666436480052) * 10 ^ 70 +
        1148406343318059969549102779435640592928262185637097305228316555028045) * 10 ^ 70 +
        3734579632611841239080318365118362546155331773187543429586399244869509) * 10 ^ 70 +
        3827228572902016828836767604759785890047829562155972301166305366447905) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (282 - x)) = _
  rw [show 283 = 92 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (283 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (283 + x) *
        remainder4Coefficient1.coeff (283 - (283 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 283 + x
  · rw [recurrence4LeadingSquare_coeff_high (283 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (283 - (283 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_283 :
    recurrence4Scalar1Left.coeff 283 =
      -(((((129979270478823902688241901 * 10 ^ 70 +
        6781418481261392051066654948481437572063779890088861457201021127418568) * 10 ^ 70 +
        0526962815066685755132257333086041170960074343560164967263092649032177) * 10 ^ 70 +
        0046388115973177911942844423386048521633904097752058798885739695281854) * 10 ^ 70 +
        3985461748793216755804833289963006367546320671038522911329450545297537) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (283 - x)) = _
  rw [show 284 = 93 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (284 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (284 + x) *
        remainder4Coefficient1.coeff (284 - (284 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 284 + x
  · rw [recurrence4LeadingSquare_coeff_high (284 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (284 - (284 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_284 :
    recurrence4Scalar1Left.coeff 284 =
      (((((102412148504556180316484793 * 10 ^ 70 +
        5326407825926190530679642079687587641428720283821785184277009933972341) * 10 ^ 70 +
        5140968164920178163837815736144713694033983420074939755774128038476743) * 10 ^ 70 +
        7134438686496952359461803888616812265027798648477387660972078814659205) * 10 ^ 70 +
        0546985333258373428148499051148363494567771702771913999300340926306816) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (284 - x)) = _
  rw [show 285 = 94 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (285 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (285 + x) *
        remainder4Coefficient1.coeff (285 - (285 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 285 + x
  · rw [recurrence4LeadingSquare_coeff_high (285 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (285 - (285 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_285 :
    recurrence4Scalar1Left.coeff 285 =
      -(((((78646263623046787531774876 * 10 ^ 70 +
        0673067489231970751377051822464403834727677619244289342212651644600079) * 10 ^ 70 +
        6750656568112028670504971002261644034328672229009695249340939945291066) * 10 ^ 70 +
        6090669291196974993998851493625184075143501483867829843015586141530422) * 10 ^ 70 +
        1149868912542707760532769898034991744606024703293683904698799573644352) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (285 - x)) = _
  rw [show 286 = 95 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (286 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (286 + x) *
        remainder4Coefficient1.coeff (286 - (286 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 286 + x
  · rw [recurrence4LeadingSquare_coeff_high (286 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (286 - (286 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_286 :
    recurrence4Scalar1Left.coeff 286 =
      (((((58947857956944941114927075 * 10 ^ 70 +
        2961093340436965661495907604399445451011039154437209892281390625512792) * 10 ^ 70 +
        7290670350552656461159339433192580888452211476769952292837119649668690) * 10 ^ 70 +
        9500764713235966172772100521805441635243626359224471795060889207868261) * 10 ^ 70 +
        7088753185817405654105040586958954473965519201564614543913181781567803) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (286 - x)) = _
  rw [show 287 = 96 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (287 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (287 + x) *
        remainder4Coefficient1.coeff (287 - (287 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 287 + x
  · rw [recurrence4LeadingSquare_coeff_high (287 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (287 - (287 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_287 :
    recurrence4Scalar1Left.coeff 287 =
      -(((((43167093465760633405513203 * 10 ^ 70 +
        2198194344685443631578625661245896936467045545388172082888189549784986) * 10 ^ 70 +
        0942450536641450932927077789505529573402380847784926333508647843879750) * 10 ^ 70 +
        0789626036207719327969573576972358983914649483492366902970419866402889) * 10 ^ 70 +
        0226736452891949347788501244620125262564259303984540341727283333504355) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (287 - x)) = _
  rw [show 288 = 97 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (288 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (288 + x) *
        remainder4Coefficient1.coeff (288 - (288 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 288 + x
  · rw [recurrence4LeadingSquare_coeff_high (288 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (288 - (288 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_288 :
    recurrence4Scalar1Left.coeff 288 =
      (((((30904553521564095191834997 * 10 ^ 70 +
        9113130825857597881882506460695009045034627693412914966931638820154183) * 10 ^ 70 +
        2654438461687818203228503278309266064487287836309741371192079305596761) * 10 ^ 70 +
        3775898105437550207871798883537806439421791869814464520877853798930055) * 10 ^ 70 +
        3117725403976800733361351888261060328754679781521974650706023009579759) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (288 - x)) = _
  rw [show 289 = 98 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (289 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (289 + x) *
        remainder4Coefficient1.coeff (289 - (289 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 289 + x
  · rw [recurrence4LeadingSquare_coeff_high (289 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (289 - (289 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_289 :
    recurrence4Scalar1Left.coeff 289 =
      -(((((21639611731758596627418819 * 10 ^ 70 +
        4130167611079429824954443777454699026800587064004652138280680116102993) * 10 ^ 70 +
        9975416306341917433695246804665471167820838367190397521146103614458429) * 10 ^ 70 +
        3045283222522070842229693455695618427813479204384331098950597693094955) * 10 ^ 70 +
        8463058219055809319780776304061384251503456248202105266821179341653816) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (289 - x)) = _
  rw [show 290 = 99 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (290 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (290 + x) *
        remainder4Coefficient1.coeff (290 - (290 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 290 + x
  · rw [recurrence4LeadingSquare_coeff_high (290 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (290 - (290 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_290 :
    recurrence4Scalar1Left.coeff 290 =
      (((((14821783427065479393337710 * 10 ^ 70 +
        3924163677127883488161813782240296001217186770119323103163648522392114) * 10 ^ 70 +
        8461807880283563849824490963911531803335909857124854361479332371226691) * 10 ^ 70 +
        7362970395559450023099113479221441721960946793027526516686189626116078) * 10 ^ 70 +
        0699111133044408901352513827501788643358079266150289553536303822412344) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (290 - x)) = _
  rw [show 291 = 100 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (291 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (291 + x) *
        remainder4Coefficient1.coeff (291 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 291 + x
  · rw [recurrence4LeadingSquare_coeff_high (291 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (291 - (291 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_291 :
    recurrence4Scalar1Left.coeff 291 =
      -(((((9929755834468308176532991 * 10 ^ 70 +
        8683864692316515904755419360925746503455910064125111575733499687087193) * 10 ^ 70 +
        3531262856382635491582890890329005122058194329700726826943408279427392) * 10 ^ 70 +
        1386710274033332637579496081592374707205196005442226029622277245517162) * 10 ^ 70 +
        5503475276605379362096443552254612449648975675251423340104087654994822) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (291 - x)) = _
  rw [show 292 = 101 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (292 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (292 + x) *
        remainder4Coefficient1.coeff (292 - (292 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 292 + x
  · rw [recurrence4LeadingSquare_coeff_high (292 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (292 - (292 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_292 :
    recurrence4Scalar1Left.coeff 292 =
      (((((6504534150005467083926656 * 10 ^ 70 +
        1282320554766604919960284237998420747174295752293443558537226135399556) * 10 ^ 70 +
        3431543477304203539481239971349009959378079795346504211546245211160329) * 10 ^ 70 +
        3672056632966959645691056869261384979595927884240760444391768023346292) * 10 ^ 70 +
        5842548542345199671359184220834007563698415257448894718450266175098640) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (292 - x)) = _
  rw [show 293 = 102 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (293 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (293 + x) *
        remainder4Coefficient1.coeff (293 - (293 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 293 + x
  · rw [recurrence4LeadingSquare_coeff_high (293 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (293 - (293 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_293 :
    recurrence4Scalar1Left.coeff 293 =
      -(((((4163488109843625097217703 * 10 ^ 70 +
        8710458865608296614453511976258792329992224653972889074550331333126187) * 10 ^ 70 +
        8080471149054886535332041120931813175707699884114523449334206927466152) * 10 ^ 70 +
        4332429665062078338261290157620724497309596115577975338693031352263770) * 10 ^ 70 +
        9047559931591109494009872827023470007732190840785352193232676125212515) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (293 - x)) = _
  rw [show 294 = 103 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (294 + x) *
        remainder4Coefficient1.coeff (294 - (294 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 294 + x
  · rw [recurrence4LeadingSquare_coeff_high (294 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (294 - (294 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_294 :
    recurrence4Scalar1Left.coeff 294 =
      (((((2601509660805825430143427 * 10 ^ 70 +
        0628415351903752139865620826906098573122210352118416946139280993669751) * 10 ^ 70 +
        2053141023550548427095489368216068343997359209191698565714498843963977) * 10 ^ 70 +
        8687021656378408602241724413314470772045353323252587112979085852314476) * 10 ^ 70 +
        9815000905742111994602414783657739844474964741954791796648723032687294) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (294 - x)) = _
  rw [show 295 = 104 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (295 + x) *
        remainder4Coefficient1.coeff (295 - (295 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 295 + x
  · rw [recurrence4LeadingSquare_coeff_high (295 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (295 - (295 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_295 :
    recurrence4Scalar1Left.coeff 295 =
      -(((((1584418174603636854623894 * 10 ^ 70 +
        7457372838277322565493414561919281556940942631828662055462525521750741) * 10 ^ 70 +
        9219307702081296413736219767240870509374765131565770857105614532988581) * 10 ^ 70 +
        6666479999270658157968990980053630811928391178446909262813632765221688) * 10 ^ 70 +
        3140542841957735987052576837825113396662857814196428301884621059006167) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (295 - x)) = _
  rw [show 296 = 105 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (296 + x) *
        remainder4Coefficient1.coeff (296 - (296 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 296 + x
  · rw [recurrence4LeadingSquare_coeff_high (296 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (296 - (296 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_296 :
    recurrence4Scalar1Left.coeff 296 =
      (((((938503737932915352196803 * 10 ^ 70 +
        7031838104900306153122688334717532819933568571853896837012449121062482) * 10 ^ 70 +
        7343083077281095688758954261204150933167885424264066904938240466538165) * 10 ^ 70 +
        6756596791136904167798585929900034593616719650000080960489375268724422) * 10 ^ 70 +
        4297231000691980295840091263786087762893596383564166395392603632819565) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (296 - x)) = _
  rw [show 297 = 106 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (297 + x) *
        remainder4Coefficient1.coeff (297 - (297 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 297 + x
  · rw [recurrence4LeadingSquare_coeff_high (297 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (297 - (297 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_297 :
    recurrence4Scalar1Left.coeff 297 =
      -(((((538905191273679242991139 * 10 ^ 70 +
        0737712375930164702481853006376459845609353656499240886500348367966063) * 10 ^ 70 +
        3959652567495977850108508551741605767363468959317623412638781847240815) * 10 ^ 70 +
        9113134272266413595061147981519808985200703733842458275797126004950237) * 10 ^ 70 +
        6440563024109755568209425295828610793092658030919392434676356686948317) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (297 - x)) = _
  rw [show 298 = 107 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (298 + x) *
        remainder4Coefficient1.coeff (298 - (298 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 298 + x
  · rw [recurrence4LeadingSquare_coeff_high (298 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (298 - (298 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_298 :
    recurrence4Scalar1Left.coeff 298 =
      (((((298505724106808136595033 * 10 ^ 70 +
        9709070564831079664314730560616275766885773761699838349703577911722979) * 10 ^ 70 +
        4666039651821535305502248030938525385327437302797961535128400837660293) * 10 ^ 70 +
        3076206769853532853719875287437604182688447762052683526057340356187198) * 10 ^ 70 +
        9734875493012384103754336620891399471814561020121095015024767676855276) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (298 - x)) = _
  rw [show 299 = 108 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (299 + x) *
        remainder4Coefficient1.coeff (299 - (299 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 299 + x
  · rw [recurrence4LeadingSquare_coeff_high (299 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (299 - (299 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_299 :
    recurrence4Scalar1Left.coeff 299 =
      -(((((158246961392889599965573 * 10 ^ 70 +
        1216253707406683204750469025865964402697930956704691617816226931606470) * 10 ^ 70 +
        1080540260055573928553431531236933834091400398154021413528755258736985) * 10 ^ 70 +
        5901675602514607872988715347256236689340256790781050653333692685973440) * 10 ^ 70 +
        7144417128423498455681695701727084821554659165287102354043109532969528) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (299 - x)) = _
  rw [show 300 = 109 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (300 + x) *
        remainder4Coefficient1.coeff (300 - (300 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 300 + x
  · rw [recurrence4LeadingSquare_coeff_high (300 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (300 - (300 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_300 :
    recurrence4Scalar1Left.coeff 300 =
      (((((79212140155311631548758 * 10 ^ 70 +
        8318656244861817499403356616477524120221511835825944084321468890731517) * 10 ^ 70 +
        1139793058659837384801232105355998205643372947481290899317571179300769) * 10 ^ 70 +
        8703991623657761256818610640072311990112097702845452128929001135376218) * 10 ^ 70 +
        9539223415309285859339998869029309396018774143208271854086544226152903) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (300 - x)) = _
  rw [show 301 = 110 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (301 + x) *
        remainder4Coefficient1.coeff (301 - (301 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 301 + x
  · rw [recurrence4LeadingSquare_coeff_high (301 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (301 - (301 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_301 :
    recurrence4Scalar1Left.coeff 301 =
      -(((((36479106844970464686947 * 10 ^ 70 +
        6060617661163451945429089100024049049348580869188810352245111552075367) * 10 ^ 70 +
        8392706079995106294282159454344517900373390393003522949531259058444068) * 10 ^ 70 +
        2794335450082803143889822674753117730773615007443654386223258780896549) * 10 ^ 70 +
        2045683004396889839692918999601834050142169063510937638994335807456927) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (301 - x)) = _
  rw [show 302 = 111 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (302 + x) *
        remainder4Coefficient1.coeff (302 - (302 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 302 + x
  · rw [recurrence4LeadingSquare_coeff_high (302 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (302 - (302 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_302 :
    recurrence4Scalar1Left.coeff 302 =
      (((((14550145322564285157226 * 10 ^ 70 +
        7476216100452526860544829139974260693790515193845072551228715438784690) * 10 ^ 70 +
        5034468966329809721840029465682181417758637032740902828752322500728999) * 10 ^ 70 +
        3241787280063746293096774391189328490138559206596621712678357903246758) * 10 ^ 70 +
        0535181431131280234098859506187247379763479850185053957091836774996546) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (302 - x)) = _
  rw [show 303 = 112 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (303 + x) *
        remainder4Coefficient1.coeff (303 - (303 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 303 + x
  · rw [recurrence4LeadingSquare_coeff_high (303 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (303 - (303 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_303 :
    recurrence4Scalar1Left.coeff 303 =
      -(((((4082481589372699592769 * 10 ^ 70 +
        4784468977610538497695348203399379621685163164704765878886257426138894) * 10 ^ 70 +
        2647997032559623389320163877996168790110694197622225772677114508243859) * 10 ^ 70 +
        2649670812239917990817666714387071015074353503325864293235989616133037) * 10 ^ 70 +
        6328880940571725237956212947197804226784565545349673074298899888793313) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (303 - x)) = _
  rw [show 304 = 113 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (304 + x) *
        remainder4Coefficient1.coeff (304 - (304 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 304 + x
  · rw [recurrence4LeadingSquare_coeff_high (304 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (304 - (304 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_304 :
    recurrence4Scalar1Left.coeff 304 =
      -(((((369168070521994027473 * 10 ^ 70 +
        7672226584054724927715799839667052894822486621720303606285271588618594) * 10 ^ 70 +
        9451747702104204983618348523991233326182274459202175314620996091582874) * 10 ^ 70 +
        2856806268678165405229282196710342636676754816280858677749267372191369) * 10 ^ 70 +
        9172973200354116715773504865652486246223097998060647218396549503617272) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (304 - x)) = _
  rw [show 305 = 114 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (305 + x) *
        remainder4Coefficient1.coeff (305 - (305 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 305 + x
  · rw [recurrence4LeadingSquare_coeff_high (305 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (305 - (305 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_305 :
    recurrence4Scalar1Left.coeff 305 =
      (((((1859537029476705585357 * 10 ^ 70 +
        0796946414303068938343561506973300116966155446538464636644736558482045) * 10 ^ 70 +
        3970942586642570259065183909432489858492521259579157776830585170161592) * 10 ^ 70 +
        6282628412520803241718606318555312057821228666169522215504037705604768) * 10 ^ 70 +
        2416693839448386715553191491707851852681497633999829315651823630599259) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (305 - x)) = _
  rw [show 306 = 115 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (306 + x) *
        remainder4Coefficient1.coeff (306 - (306 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 306 + x
  · rw [recurrence4LeadingSquare_coeff_high (306 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (306 - (306 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_306 :
    recurrence4Scalar1Left.coeff 306 =
      -(((((2026042089798332336952 * 10 ^ 70 +
        6432080467971793745308605821339139514532404939982733930819982498317648) * 10 ^ 70 +
        0282669405248144980200964313187547147893903877311104731482149343307758) * 10 ^ 70 +
        9713839725568718309101970910286350966200172672729820422152890520352283) * 10 ^ 70 +
        0715181517929347403498883080991904558265328950127282837556163709515548) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (306 - x)) = _
  rw [show 307 = 116 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (307 + x) *
        remainder4Coefficient1.coeff (307 - (307 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 307 + x
  · rw [recurrence4LeadingSquare_coeff_high (307 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (307 - (307 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_307 :
    recurrence4Scalar1Left.coeff 307 =
      (((((1696735036231757251746 * 10 ^ 70 +
        2420890270346940762540037196783706893631541114824589988325720676140663) * 10 ^ 70 +
        1191827800205712545904531059006353579831390670086194820335161137971832) * 10 ^ 70 +
        8796226236613906785297490717400322641978500842468503631929064580469472) * 10 ^ 70 +
        2572912031689111273778532774464187752110975917867796626905006414663568) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (307 - x)) = _
  rw [show 308 = 117 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (308 + x) *
        remainder4Coefficient1.coeff (308 - (308 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 308 + x
  · rw [recurrence4LeadingSquare_coeff_high (308 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (308 - (308 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_308 :
    recurrence4Scalar1Left.coeff 308 =
      -(((((1257140970557205035620 * 10 ^ 70 +
        4770028208996739799469408518665084731939471968557761291693479721638946) * 10 ^ 70 +
        0343801552997333197480156656570752018934076070629382542578513095063919) * 10 ^ 70 +
        1613005631304499124739646278116947523272315071425693372153850452165419) * 10 ^ 70 +
        0555609995333404639463643876686215612472492927465386992744495226848229) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (308 - x)) = _
  rw [show 309 = 118 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (309 + x) *
        remainder4Coefficient1.coeff (309 - (309 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 309 + x
  · rw [recurrence4LeadingSquare_coeff_high (309 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (309 - (309 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_309 :
    recurrence4Scalar1Left.coeff 309 =
      (((((863491282783739514710 * 10 ^ 70 +
        5591784514389128494857092640253431072213224957778974853759703500864172) * 10 ^ 70 +
        6544454920159385851113427430918552074178032977388407105416366308367601) * 10 ^ 70 +
        8571481984611945626189308705315650625470059462714329507104459202431292) * 10 ^ 70 +
        3356004166097881767138082470903288483534154300040451499456865192479708) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (309 - x)) = _
  rw [show 310 = 119 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (310 + x) *
        remainder4Coefficient1.coeff (310 - (310 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 310 + x
  · rw [recurrence4LeadingSquare_coeff_high (310 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (310 - (310 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_310 :
    recurrence4Scalar1Left.coeff 310 =
      -(((((561553586257572158609 * 10 ^ 70 +
        1839671801071905134771103594237629948074327840354518799160488395249127) * 10 ^ 70 +
        4841062925298853631283340780635091542466358248801734090340175938229421) * 10 ^ 70 +
        6280168585059875157048164987598727415528917205861502812470043274292936) * 10 ^ 70 +
        9247913402830320682534681983087353471043363046775178405982357536910517) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (310 - x)) = _
  rw [show 311 = 120 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (311 + x) *
        remainder4Coefficient1.coeff (311 - (311 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 311 + x
  · rw [recurrence4LeadingSquare_coeff_high (311 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (311 - (311 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_311 :
    recurrence4Scalar1Left.coeff 311 =
      (((((349593815646457863343 * 10 ^ 70 +
        5495145637222492748476783392231546024141785898347157278096192791332984) * 10 ^ 70 +
        6552164595939665340813723219009392872469347847191031685643254322485980) * 10 ^ 70 +
        0671856386751952679876397146571529042270718524337401060751197277886752) * 10 ^ 70 +
        2646657320210134104910856538518972109471416905619995932817825700243163) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (311 - x)) = _
  rw [show 312 = 121 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (312 + x) *
        remainder4Coefficient1.coeff (312 - (312 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 312 + x
  · rw [recurrence4LeadingSquare_coeff_high (312 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (312 - (312 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_312 :
    recurrence4Scalar1Left.coeff 312 =
      -(((((209619174859093697046 * 10 ^ 70 +
        8331644631619242327366167341350649340480321721755106551944897746817968) * 10 ^ 70 +
        5179119869480648552280431814551932723034174519083154782032553250007769) * 10 ^ 70 +
        1849000508150264951792584650858384634336550571923773808784507477325060) * 10 ^ 70 +
        8976247632440756811291935753252261001418377740436924650865763106630076) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (312 - x)) = _
  rw [show 313 = 122 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (313 + x) *
        remainder4Coefficient1.coeff (313 - (313 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 313 + x
  · rw [recurrence4LeadingSquare_coeff_high (313 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (313 - (313 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_313 :
    recurrence4Scalar1Left.coeff 313 =
      (((((121459228004893647603 * 10 ^ 70 +
        2456349906761169319628765615836977995949764128550205121061379155555057) * 10 ^ 70 +
        8471745697117898359844386617301861309032545027621007065322271910812193) * 10 ^ 70 +
        0430390088747260975250543535394131180209341956581109943958894769285386) * 10 ^ 70 +
        8772840115739799248516244883642363973044898775880722936931259852232281) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (313 - x)) = _
  rw [show 314 = 123 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (314 + x) *
        remainder4Coefficient1.coeff (314 - (314 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 314 + x
  · rw [recurrence4LeadingSquare_coeff_high (314 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (314 - (314 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_314 :
    recurrence4Scalar1Left.coeff 314 =
      -(((((68104318182377182089 * 10 ^ 70 +
        2014856911550883284172963380195767051399223554035061370822659592101842) * 10 ^ 70 +
        9240413996225561456552996522072589195598070544113961410672924425169457) * 10 ^ 70 +
        1515582100908098576543178884572535465171504255955163328617993606373865) * 10 ^ 70 +
        4889238901952129708482603497951867030369869895619234295683275828390529) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (314 - x)) = _
  rw [show 315 = 124 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (315 + x) *
        remainder4Coefficient1.coeff (315 - (315 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 315 + x
  · rw [recurrence4LeadingSquare_coeff_high (315 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (315 - (315 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_315 :
    recurrence4Scalar1Left.coeff 315 =
      (((((36948426982327170076 * 10 ^ 70 +
        3601279215581879238799779652646571353737580489061752204471702736280739) * 10 ^ 70 +
        3234713243810729818299694555331884144823182941569352849207972906446067) * 10 ^ 70 +
        6899041736251438948920337997315099165021757507440930512499417721453651) * 10 ^ 70 +
        1981618009557710882532743453829212555632362953630269099884637314264510) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (315 - x)) = _
  rw [show 316 = 125 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (316 + x) *
        remainder4Coefficient1.coeff (316 - (316 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 316 + x
  · rw [recurrence4LeadingSquare_coeff_high (316 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (316 - (316 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_316 :
    recurrence4Scalar1Left.coeff 316 =
      -(((((19360972730896280550 * 10 ^ 70 +
        7096990024385375530333986732965278068608414382990322094611804430715058) * 10 ^ 70 +
        3665714241812979666561098094280703279173550212260325658557507018316092) * 10 ^ 70 +
        2460357662418097049669412800438119675162680020280695419379103292545904) * 10 ^ 70 +
        7521509977925338710235884672830376362237675176086061027425780279318842) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (316 - x)) = _
  rw [show 317 = 126 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (317 + x) *
        remainder4Coefficient1.coeff (317 - (317 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 317 + x
  · rw [recurrence4LeadingSquare_coeff_high (317 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (317 - (317 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_317 :
    recurrence4Scalar1Left.coeff 317 =
      (((((9761243882719601944 * 10 ^ 70 +
        6335390937723085314303607880278762335377650006194309027442586813763280) * 10 ^ 70 +
        6800399030420649191302554073367127539819154124288276664196261137568642) * 10 ^ 70 +
        1978382025350514596233492732767897402890382659848640192029846731316906) * 10 ^ 70 +
        2527745912975204884642070843961885176842496225478183498500624948817541) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (317 - x)) = _
  rw [show 318 = 127 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (318 + x) *
        remainder4Coefficient1.coeff (318 - (318 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 318 + x
  · rw [recurrence4LeadingSquare_coeff_high (318 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (318 - (318 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_318 :
    recurrence4Scalar1Left.coeff 318 =
      -(((((4702011145023603980 * 10 ^ 70 +
        6268850673254962672991696401337116028477776604098098581808147001874200) * 10 ^ 70 +
        3790541266222064536866767987913763561859773912188118125798667265013541) * 10 ^ 70 +
        7764421250811643631872168876690671020163945953789203191983956339761615) * 10 ^ 70 +
        4951879260308005330402026867989015409432722344014099163023413312996115) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (318 - x)) = _
  rw [show 319 = 128 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (319 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (319 + x) *
        remainder4Coefficient1.coeff (319 - (319 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 319 + x
  · rw [recurrence4LeadingSquare_coeff_high (319 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (319 - (319 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_319 :
    recurrence4Scalar1Left.coeff 319 =
      (((((2136494512867850827 * 10 ^ 70 +
        6870269382161906340383038330313703500778090136531198044689069462584957) * 10 ^ 70 +
        2528552868296909733008737140426381534725689647271987982966474905187541) * 10 ^ 70 +
        2979713950961268078204461031037261954020429971838456039143114484748122) * 10 ^ 70 +
        2581943774800699592007319476747179551621515694711015773802147569033624) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 320,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (319 - x)) = _
  rw [show 320 = 129 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (320 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (320 + x) *
        remainder4Coefficient1.coeff (320 - (320 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 320 + x
  · rw [recurrence4LeadingSquare_coeff_high (320 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (320 - (320 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_320 :
    recurrence4Scalar1Left.coeff 320 =
      -(((((892826103881173593 * 10 ^ 70 +
        2137026365276225792491258434718053432360875063751983228269611454243709) * 10 ^ 70 +
        3036239565655509262309113613869312346537686287455547412694817633537568) * 10 ^ 70 +
        9347302800067742999885528039744086082365130066010172958180232295481789) * 10 ^ 70 +
        1574081103910193743781974059625702986754038862570993724110463480862176) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 321,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (320 - x)) = _
  rw [show 321 = 130 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (321 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (321 + x) *
        remainder4Coefficient1.coeff (321 - (321 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 321 + x
  · rw [recurrence4LeadingSquare_coeff_high (321 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (321 - (321 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_321 :
    recurrence4Scalar1Left.coeff 321 =
      (((((323311104175079773 * 10 ^ 70 +
        4785318480861609991942195428572516260843429682761632096471556580071508) * 10 ^ 70 +
        7175531584465729455885839151376836671157754934082985279011820317426060) * 10 ^ 70 +
        1062685667292467618172156370614033281259625072730015360744759251237643) * 10 ^ 70 +
        9514699749735564367783374195341548966780443297830418918324775803334517) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 322,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (321 - x)) = _
  rw [show 322 = 131 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (322 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (322 + x) *
        remainder4Coefficient1.coeff (322 - (322 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 322 + x
  · rw [recurrence4LeadingSquare_coeff_high (322 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (322 - (322 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_322 :
    recurrence4Scalar1Left.coeff 322 =
      -(((((82619800082825421 * 10 ^ 70 +
        1881583189052069792686692525964221260879475934144143124866579118491288) * 10 ^ 70 +
        0929944633517737212387703209249595876372511849906002542015411960993314) * 10 ^ 70 +
        2087977763805953528434713136174070209375048699112830165135307768417252) * 10 ^ 70 +
        0805725930502623783729860507011302397141344438388118180663843220058670) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 323,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (322 - x)) = _
  rw [show 323 = 132 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (323 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (323 + x) *
        remainder4Coefficient1.coeff (323 - (323 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 323 + x
  · rw [recurrence4LeadingSquare_coeff_high (323 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (323 - (323 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_323 :
    recurrence4Scalar1Left.coeff 323 =
      -(((((6372292869014522 * 10 ^ 70 +
        0717129633836327006759414077743692762757433843255140158287865141817898) * 10 ^ 70 +
        2585544596918897858433650241731296071573846783229443380644666592416606) * 10 ^ 70 +
        7478099577599895415400349223685516922296535218551711553907894670770694) * 10 ^ 70 +
        9975010158599862727109872980414066784435421047149911709701097081147714) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 324,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (323 - x)) = _
  rw [show 324 = 133 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (324 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (324 + x) *
        remainder4Coefficient1.coeff (324 - (324 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 324 + x
  · rw [recurrence4LeadingSquare_coeff_high (324 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (324 - (324 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_324 :
    recurrence4Scalar1Left.coeff 324 =
      (((((30579051699658885 * 10 ^ 70 +
        5513895268853522234943644876529411444356416817121882613730757224773257) * 10 ^ 70 +
        1510712758210098313622086906459803333614964035194201862817756660421156) * 10 ^ 70 +
        4724451806960401798652151427474369353729664545153372251926854126041828) * 10 ^ 70 +
        5502388501826598749394371007211453792762656253433752806937816659088084) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 325,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (324 - x)) = _
  rw [show 325 = 134 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (325 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (325 + x) *
        remainder4Coefficient1.coeff (325 - (325 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 325 + x
  · rw [recurrence4LeadingSquare_coeff_high (325 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (325 - (325 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_325 :
    recurrence4Scalar1Left.coeff 325 =
      -(((((30381930179249415 * 10 ^ 70 +
        9524418668185145439671530770405873481990559828543003894390423769690423) * 10 ^ 70 +
        5537315334000286969217537978388408594117074866473327514532702091692150) * 10 ^ 70 +
        4372356447006964420420290480061517788674070008402702900650757808281929) * 10 ^ 70 +
        5915880384046744646945666091107184754748312531770244334138877086801098) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 326,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (325 - x)) = _
  rw [show 326 = 135 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (326 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (326 + x) *
        remainder4Coefficient1.coeff (326 - (326 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 326 + x
  · rw [recurrence4LeadingSquare_coeff_high (326 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (326 - (326 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_326 :
    recurrence4Scalar1Left.coeff 326 =
      (((((23195013159806227 * 10 ^ 70 +
        3380448689038159202874732612029599831846643100947974284453952067377694) * 10 ^ 70 +
        0517096823045240028749079907077856059116659448711453390815432530094314) * 10 ^ 70 +
        6860497901001877418530817588637599519067310118406403986798436637536183) * 10 ^ 70 +
        1399541471923285712792052765638010666338551984777274144193163167669243) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 327,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (326 - x)) = _
  rw [show 327 = 136 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (327 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (327 + x) *
        remainder4Coefficient1.coeff (327 - (327 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 327 + x
  · rw [recurrence4LeadingSquare_coeff_high (327 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (327 - (327 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_327 :
    recurrence4Scalar1Left.coeff 327 =
      -(((((15688945630511665 * 10 ^ 70 +
        7350752345542952368474894187857819057559000957385713088663982109646983) * 10 ^ 70 +
        4669338091457481422059348870994912160017828927065357409724694501210299) * 10 ^ 70 +
        6236570121361983986722171036289654289274616275410895828669775166883166) * 10 ^ 70 +
        1597369496925709391757720037921558483839601720351158982251463034674633) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 328,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (327 - x)) = _
  rw [show 328 = 137 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (328 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (328 + x) *
        remainder4Coefficient1.coeff (328 - (328 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 328 + x
  · rw [recurrence4LeadingSquare_coeff_high (328 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (328 - (328 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_328 :
    recurrence4Scalar1Left.coeff 328 =
      (((((9859091026544070 * 10 ^ 70 +
        7366975950690620124732256746922687111685371729241069274449426559475348) * 10 ^ 70 +
        2344795068481708662776765721960878132895532386461004201369526563702187) * 10 ^ 70 +
        6142787728259442412977208062689395271341184436124780339444138375157183) * 10 ^ 70 +
        3248323993379951970990340623930281408442804205462735485124989844958560) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 329,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (328 - x)) = _
  rw [show 329 = 138 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (329 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (329 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (329 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_329 :
    recurrence4Scalar1Left.coeff 329 =
      -(((((5882509406296779 * 10 ^ 70 +
        3294669478765850329860529049364122220563511617512885117280143109850647) * 10 ^ 70 +
        2019601529430886635411066528146453100057425799371892725405680165981591) * 10 ^ 70 +
        2074425996598470398764649327756563716327424100778036242541426089674069) * 10 ^ 70 +
        3970905856292056293620667116064554037416700034938483564335670291556452) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 330,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (329 - x)) = _
  rw [show 330 = 139 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (330 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (330 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (330 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_330 :
    recurrence4Scalar1Left.coeff 330 =
      (((((3371865490747043 * 10 ^ 70 +
        7924908554061287136749465213329432641509780804498705771087501593552873) * 10 ^ 70 +
        1704946435375132572743993913364591701692054533792287086383596036437278) * 10 ^ 70 +
        9042933681833590064652279593874797712231726455201342737071735475160038) * 10 ^ 70 +
        4110496432209455991535939947599514594281477416918835760383261143520021) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 331,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (330 - x)) = _
  rw [show 331 = 140 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 29 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (331 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (331 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (331 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_331 :
    recurrence4Scalar1Left.coeff 331 =
      -(((((1869868695295900 * 10 ^ 70 +
        9689678398648764983046998140683603861680046607427177283331258896528901) * 10 ^ 70 +
        2190067311956919866067821803487728102640713033889273116906961637464676) * 10 ^ 70 +
        6552003745599665772877070328361101939535503007803597440538917958219904) * 10 ^ 70 +
        5469260118326920264011213526762245831187024194124661589155069926880009) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 332,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (331 - x)) = _
  rw [show 332 = 141 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 28 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (332 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (332 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (332 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_332 :
    recurrence4Scalar1Left.coeff 332 =
      (((((1007716174659003 * 10 ^ 70 +
        7079655937116559693809692127283197025913390955951880732704357783391215) * 10 ^ 70 +
        5056267739571221462291452434431491704438715856292222517344282677935721) * 10 ^ 70 +
        8244866612913319089442783508215280228966795219708104171833935441556428) * 10 ^ 70 +
        2904534633866517047157867048806808058088977660533495893879459897546034) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 333,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (332 - x)) = _
  rw [show 333 = 142 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 27 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (333 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (333 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (333 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_333 :
    recurrence4Scalar1Left.coeff 333 =
      -(((((529368849940067 * 10 ^ 70 +
        8330461526729872643130336548459537796854339339783464422338360121282547) * 10 ^ 70 +
        2183505405580020111593734455904399572888829766242761552240371935362561) * 10 ^ 70 +
        7461504785397702192664107434522973235056673543103157832447943069721118) * 10 ^ 70 +
        1612540263406663568370053307523175850657986912564661742612517105164271) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 334,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (333 - x)) = _
  rw [show 334 = 143 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 26 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (334 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (334 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (334 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_334 :
    recurrence4Scalar1Left.coeff 334 =
      (((((271625118684423 * 10 ^ 70 +
        1335790303530192928919069194040771750995999878149556736191539951231123) * 10 ^ 70 +
        7076604845921952223171878616126180027418176983003599680788429594947907) * 10 ^ 70 +
        7472096512869455932426889878874108382414682320243860783104738546899340) * 10 ^ 70 +
        1892276454135685924899985070183799362852777338935232261249967773267921) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 335,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (334 - x)) = _
  rw [show 335 = 144 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 25 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (335 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (335 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (335 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_335 :
    recurrence4Scalar1Left.coeff 335 =
      -(((((136331852337229 * 10 ^ 70 +
        5402304403099714244776644841631884934382802757830116186393912101819944) * 10 ^ 70 +
        4703876843581930767890183644386782613600130261835987871256247188867538) * 10 ^ 70 +
        5384615248178316222936260769231729098204266394974926934352037889551546) * 10 ^ 70 +
        7571979137438071368039271693188997653576096804120009673139238320106268) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 336,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (335 - x)) = _
  rw [show 336 = 145 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 24 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (336 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (336 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (336 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_336 :
    recurrence4Scalar1Left.coeff 336 =
      (((((66999500535268 * 10 ^ 70 +
        4109769534057254689329484194317947242069233284139274965792547440194162) * 10 ^ 70 +
        1148617713878801847007861702178886636139489600265815211271217177011740) * 10 ^ 70 +
        1433508534212444508041309025051061878428770804119510056147523953382596) * 10 ^ 70 +
        3229331420722056305786977090434604554347754400478669712821468762170929) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 337,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (336 - x)) = _
  rw [show 337 = 146 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 23 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (337 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (337 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (337 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_337 :
    recurrence4Scalar1Left.coeff 337 =
      -(((((32261164232005 * 10 ^ 70 +
        3480904964042819123708358085797784237076166314399421172618230717285922) * 10 ^ 70 +
        2833330981071406052670793957421803100997216631660768347544853933790328) * 10 ^ 70 +
        4368278970836009234409194782436768290109249613052557329711508991722894) * 10 ^ 70 +
        8254176384693086164860834529510157067356884009852568690053623331845176) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 338,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (337 - x)) = _
  rw [show 338 = 147 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 22 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (338 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (338 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (338 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_338 :
    recurrence4Scalar1Left.coeff 338 =
      (((((15226440301887 * 10 ^ 70 +
        4796153614000863454535752663883633587845294052264872360059707630779566) * 10 ^ 70 +
        2616840726961423855769880210116639513612972799864297647945284129161294) * 10 ^ 70 +
        6003768072770500784397914476548514726405576890514288390967391257813647) * 10 ^ 70 +
        8670156909912973588834703589947157383521093477654213158342857814665614) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 339,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (338 - x)) = _
  rw [show 339 = 148 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 21 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (339 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (339 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (339 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_339 :
    recurrence4Scalar1Left.coeff 339 =
      -(((((7045481744280 * 10 ^ 70 +
        3165262550058909392944267582658267160942863665998971812242380315007072) * 10 ^ 70 +
        3567643788688382538949021806237994171944973842873186174870680925228219) * 10 ^ 70 +
        5246777701136655702691287351865922453095095723746965958433598059453059) * 10 ^ 70 +
        0950268697122181024067807029913980904929474288936492964541650045207373) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 340,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (339 - x)) = _
  rw [show 340 = 149 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 20 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (340 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (340 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (340 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_340 :
    recurrence4Scalar1Left.coeff 340 =
      (((((3196111641972 * 10 ^ 70 +
        7826487887046743458489775620746202322459933141285432091215651017507864) * 10 ^ 70 +
        8174561687111051278851063422752447297220635024444022506384753507045140) * 10 ^ 70 +
        5380921583448875582963855992135290732011543978996518613013394167652254) * 10 ^ 70 +
        2361137357832812826517734645151730677945267069903196716202601366811886) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 341,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (340 - x)) = _
  rw [show 341 = 150 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 19 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (341 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (341 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (341 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_341 :
    recurrence4Scalar1Left.coeff 341 =
      -(((((1421231313857 * 10 ^ 70 +
        0249849655771272954005547909444618553324141222918378950753396462295969) * 10 ^ 70 +
        0740318465764999686446202475307082056234618704900770637917212762097107) * 10 ^ 70 +
        4658363466969751770672211550242230356306373282380429765740787922169244) * 10 ^ 70 +
        5914938732126477602018718586227043923432026150700397584914060820566036) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 342,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (341 - x)) = _
  rw [show 342 = 151 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 18 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (342 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (342 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (342 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_342 :
    recurrence4Scalar1Left.coeff 342 =
      (((((619300938810 * 10 ^ 70 +
        9669843547419090852130540001335760459491344384763289096576765953868277) * 10 ^ 70 +
        6538881781458637817137603579800419456962997826018515431080588779675961) * 10 ^ 70 +
        9005893015695147790397735921050458895842796562400715481277244875998475) * 10 ^ 70 +
        9164576046225989599174287320802550782348941415895665006273786167679846) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 343,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (342 - x)) = _
  rw [show 343 = 152 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 17 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (343 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (343 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (343 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_343 :
    recurrence4Scalar1Left.coeff 343 =
      -(((((264316071371 * 10 ^ 70 +
        2145686266753652200473426768167320920665395977074265835718894855646161) * 10 ^ 70 +
        1098105700033954518432911041474931272649596741883786333784503501964746) * 10 ^ 70 +
        8067208192200601597119318464301262320076400278414555062976163461093953) * 10 ^ 70 +
        9999023495864840733916593328475444758425864313934435973910287670803813) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 344,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (343 - x)) = _
  rw [show 344 = 153 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 16 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (344 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (344 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (344 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_344 :
    recurrence4Scalar1Left.coeff 344 =
      (((((110418876561 * 10 ^ 70 +
        6322090269962453347639029256271228463799300244391979158692245260168493) * 10 ^ 70 +
        4301226450985615745363370914259789293503438330329512862242699949663731) * 10 ^ 70 +
        0662651688101608948506963411398518579980896599006672396130370316136546) * 10 ^ 70 +
        0562567539056854872709523343473927240363735476321949475839782577935264) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 345,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (344 - x)) = _
  rw [show 345 = 154 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 15 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (345 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (345 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (345 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_345 :
    recurrence4Scalar1Left.coeff 345 =
      -(((((45111371729 * 10 ^ 70 +
        8617888303501166839701047908022980215901759921085353027658258687505268) * 10 ^ 70 +
        0494721840349199970468713430099288262817283524376680453592282141603198) * 10 ^ 70 +
        2963434179622912613259486995455934214834464586840645291701920537666487) * 10 ^ 70 +
        1235476218084469483949969491557739492689224378573578877908885176764766) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 346,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (345 - x)) = _
  rw [show 346 = 155 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 14 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (346 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (346 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (346 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_346 :
    recurrence4Scalar1Left.coeff 346 =
      (((((18004151386 * 10 ^ 70 +
        6909651783875763611600447945552380115641940145728134145584732823230991) * 10 ^ 70 +
        4613663635372219819932316943349415059259094310453483351514014706622795) * 10 ^ 70 +
        8869373888217170179873173492043598606503615597009241310524928025183799) * 10 ^ 70 +
        9926791516478751904442020544963409544471468678035781497265566016017879) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 347,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (346 - x)) = _
  rw [show 347 = 156 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 13 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (347 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (347 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (347 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_347 :
    recurrence4Scalar1Left.coeff 347 =
      -(((((7009649967 * 10 ^ 70 +
        2794997947836589263687929839325940648161819787930170197572684263281560) * 10 ^ 70 +
        7198468864357585312985978304819848421316819415638256143729696558266620) * 10 ^ 70 +
        6544601763651806789213680898267087704451100647460041528179783905697846) * 10 ^ 70 +
        9140950206497509098126197402510031339737110611508727154567372450201322) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 348,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (347 - x)) = _
  rw [show 348 = 157 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 12 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (348 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (348 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (348 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_348 :
    recurrence4Scalar1Left.coeff 348 =
      (((((2657586926 * 10 ^ 70 +
        3166073884875841189697622966327627356509039186891039963551899176693776) * 10 ^ 70 +
        9383695151531740333302400571099402658707831823484087223005285447542111) * 10 ^ 70 +
        6395523504156681591824036871629395264256878600851649230926688073091356) * 10 ^ 70 +
        7355371960674811593694250638847494022159454740629756888569570773665079) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 349,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (348 - x)) = _
  rw [show 349 = 158 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 11 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (349 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (349 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (349 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_349 :
    recurrence4Scalar1Left.coeff 349 =
      -(((((978952660 * 10 ^ 70 +
        1132333624247932095290090604508237582980913475057099561143342092135626) * 10 ^ 70 +
        9078424452795105187835827229608827376651192817986501114313185233087734) * 10 ^ 70 +
        8473274614935214620670931170977498001095877699795776468889947558936139) * 10 ^ 70 +
        5671171555926266780901863962586311404474722347498440002724001603399230) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 350,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (349 - x)) = _
  rw [show 350 = 159 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 10 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (350 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (350 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (350 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_350 :
    recurrence4Scalar1Left.coeff 350 =
      (((((349332866 * 10 ^ 70 +
        1487798874933734401974904029100840130475212804922410598093190064875393) * 10 ^ 70 +
        3549306224056646348176914112663293244529331463733138487352259798033386) * 10 ^ 70 +
        4367539753245060977003831060978767834067039948311212160466227198484992) * 10 ^ 70 +
        9142907502693119288923267411259154340610670670886013282361087242785659) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 351,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (350 - x)) = _
  rw [show 351 = 160 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 9 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (351 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (351 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (351 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_351 :
    recurrence4Scalar1Left.coeff 351 =
      -(((((120286399 * 10 ^ 70 +
        0795038765951331920897207116586230168831949434851944686391246222478535) * 10 ^ 70 +
        3170646420601931149474393535555852897975475092641430907566193859481786) * 10 ^ 70 +
        9931412122058466957116036521421166058537805424629585413411461700837005) * 10 ^ 70 +
        4305759525204934575818925362936159859111166508380130147864848546677256) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 352,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (351 - x)) = _
  rw [show 352 = 161 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 8 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (352 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (352 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (352 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_352 :
    recurrence4Scalar1Left.coeff 352 =
      (((((39750395 * 10 ^ 70 +
        4895933724983486957291997673262798359616458752261978712710696761109721) * 10 ^ 70 +
        9690490479356282465846809456540700770584571548990898758513610632271569) * 10 ^ 70 +
        8000131154726115542605536590617349564753545793296735355571021421996366) * 10 ^ 70 +
        7098130896101350151410972019116849254807403306547578922430607669640692) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 353,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (352 - x)) = _
  rw [show 353 = 162 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 7 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (353 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (353 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (353 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_353 :
    recurrence4Scalar1Left.coeff 353 =
      -(((((12508380 * 10 ^ 70 +
        3822864057199264277008250289671112121936538592286236274624506262232969) * 10 ^ 70 +
        5211538758935952474923407541051599852913536618931787936836206180221562) * 10 ^ 70 +
        7353066898691548108641884256060364851509696060621916698499939876936286) * 10 ^ 70 +
        2729635835965326414801694891989242667758055331427046977876244108740500) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 354,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (353 - x)) = _
  rw [show 354 = 163 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 6 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (354 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (354 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (354 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_354 :
    recurrence4Scalar1Left.coeff 354 =
      (((((3702217 * 10 ^ 70 +
        6048683527745052234162796340102877244477409361896842778672857778717918) * 10 ^ 70 +
        1378792908939720899282292590522060747821464216169142366910998601633874) * 10 ^ 70 +
        4094045549776260302174692562376838102045154190706934251941268141948537) * 10 ^ 70 +
        2025915748261855018581452350036285005549716742193880653700831481580424) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 355,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (354 - x)) = _
  rw [show 355 = 164 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 5 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (355 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (355 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (355 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_355 :
    recurrence4Scalar1Left.coeff 355 =
      -(((((1008821 * 10 ^ 70 +
        7078188887706410615125952080603839580566535273510190276019296667627549) * 10 ^ 70 +
        6960559706073206808417326886987555289086788853897984522955492491276380) * 10 ^ 70 +
        2463867411540786945414342065290589124853637392750252316664262986739641) * 10 ^ 70 +
        9796620994238398601359577760997012736139317986644669469303511475087798) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 356,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (355 - x)) = _
  rw [show 356 = 165 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 4 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (356 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (356 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (356 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_356 :
    recurrence4Scalar1Left.coeff 356 =
      (((((242040 * 10 ^ 70 +
        2734782211184569437857577781202285894705612270552190508367122430379784) * 10 ^ 70 +
        0028154159435781260643288699911717190929129712933786682421754260334678) * 10 ^ 70 +
        1676746829210537340907688805310085752698742612835737999207864014248562) * 10 ^ 70 +
        2490027564600020418600592700262679685594937268070513437958773365609253) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 357,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (356 - x)) = _
  rw [show 357 = 166 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 3 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (357 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (357 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (357 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_357 :
    recurrence4Scalar1Left.coeff 357 =
      -(((((45009 * 10 ^ 70 +
        6429947153173596642186269220382339193702331069644871908110180211754309) * 10 ^ 70 +
        5437867231745068921048131476961172457100290874897304264304708309123095) * 10 ^ 70 +
        4084372780516176027991563013797734349523731932984732734297868879569307) * 10 ^ 70 +
        6214594004021226323401238639367265695268880671683511417937432467036382) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 358,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (357 - x)) = _
  rw [show 358 = 167 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 2 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (358 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (358 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (358 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_358 :
    recurrence4Scalar1Left.coeff 358 =
      (((((2522 * 10 ^ 70 +
        5473627353250655218723292126653984080577593569814931331138311581748910) * 10 ^ 70 +
        0444941501286623502366299094756145390640184595435028412202557925316629) * 10 ^ 70 +
        4934388009095920273739962114443318195907046866293496653586532263007504) * 10 ^ 70 +
        3975382954877129045779227158368187865542959522070001823308692916198060) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (358 - x)) = _
  rw [show 359 = 168 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 1 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (359 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (359 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (359 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_359 :
    recurrence4Scalar1Left.coeff 359 =
      (((((3285 * 10 ^ 70 +
        4684946195347600780689717787337192974115760272326855531161497617592677) * 10 ^ 70 +
        2657269964132117130598035816083669645967009490513332630595355675830421) * 10 ^ 70 +
        4997378310377322136942044040915842153600781778704523429889560306326127) * 10 ^ 70 +
        7924246084221425929490450624078068886351293727272941451913070811766492) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (359 - x)) = _
  rw [show 360 = 169 +
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
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (360 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (360 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (360 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_360 :
    recurrence4Scalar1Left.coeff 360 =
      -(((((2439 * 10 ^ 70 +
        7111159326811674972724991872578269905493061166865976424188110402557158) * 10 ^ 70 +
        3074489799371091814897727583871586782218233510271723569857200208303280) * 10 ^ 70 +
        3891078606433710878959895989243387948028255039710995342413589973639094) * 10 ^ 70 +
        6170694491980429154087177133016560504498613421222209562296117700433462) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (360 - x)) = _
  rw [show 361 = 170 +
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
    rw [show 63 = 31 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (361 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (361 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (361 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_361 :
    recurrence4Scalar1Left.coeff 361 =
      (((((1281 * 10 ^ 70 +
        3026419537936591367750635730823830446013824065819929617539404729556377) * 10 ^ 70 +
        7304228034957503374529507168804816981553333071287055169521268315195512) * 10 ^ 70 +
        7748175043383812473894076592194591863238353949179435229586782521382848) * 10 ^ 70 +
        2303240187442587373866573187221444245734640933006675074770160394215236) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (361 - x)) = _
  rw [show 362 = 171 +
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
    rw [show 63 = 30 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (362 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (362 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (362 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_362 :
    recurrence4Scalar1Left.coeff 362 =
      -(((((618 * 10 ^ 70 +
        3292519100409134695379961765047851174977949146156796973109956338415372) * 10 ^ 70 +
        2534400982492667807980671999130790049404194875826922639465879359774619) * 10 ^ 70 +
        3167358378072989183394801113263746305513584599206997751924099929364351) * 10 ^ 70 +
        5578251181237359865942095772817200443247309388406649831480544131453476) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (362 - x)) = _
  rw [show 363 = 172 +
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
    rw [show 63 = 29 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (363 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (363 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (363 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_363 :
    recurrence4Scalar1Left.coeff 363 =
      (((((299 * 10 ^ 70 +
        0998890255914638537770806959875256440834070846262967403238745649121076) * 10 ^ 70 +
        9899227803492068755333069395650921599742571367950437779399482921441886) * 10 ^ 70 +
        2453320011613009020037094819290724536292193682102333584060421844048833) * 10 ^ 70 +
        4014332220827166327012822261110088958210302619303569366077173062668323) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (363 - x)) = _
  rw [show 364 = 173 +
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
    rw [show 63 = 28 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (364 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (364 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (364 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_364 :
    recurrence4Scalar1Left.coeff 364 =
      -(((((149 * 10 ^ 70 +
        2606646650913087244911236140376805647780768877393350541769153505836551) * 10 ^ 70 +
        2135858228637600966357641320988686250058814036674464656472041011941957) * 10 ^ 70 +
        5156535097862686436428054144577499623781145062512414108866966119449214) * 10 ^ 70 +
        4876434431694021772123593735037298874877611465426583708012508290779253) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (364 - x)) = _
  rw [show 365 = 174 +
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
    rw [show 63 = 27 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (365 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (365 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (365 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_365 :
    recurrence4Scalar1Left.coeff 365 =
      (((((76 * 10 ^ 70 +
        3273487151685051300598831661791858694525140396988790013458473645254696) * 10 ^ 70 +
        8723640428857386799950804889451816770789325948192003177053961344549762) * 10 ^ 70 +
        4735118820421107204108316104921710323682788372439066977935644872503208) * 10 ^ 70 +
        8391588697333888273031927034784870641324403565952339767078465772921561) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (365 - x)) = _
  rw [show 366 = 175 +
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
  rw [recurrence4Scalar1Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (366 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (366 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (366 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_366 :
    recurrence4Scalar1Left.coeff 366 =
      -(((((39 * 10 ^ 70 +
        1468758905629910596849839831366868032581380920786593813955763412233008) * 10 ^ 70 +
        1828221700820030429265598331883316203270814611207625271838883513311025) * 10 ^ 70 +
        2547741186217554787974569181990505064485556528137173635268972292808932) * 10 ^ 70 +
        9183851681381670201569228756034977831936617308229891764734093797797269) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (366 - x)) = _
  rw [show 367 = 176 +
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
    rw [show 63 = 25 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (367 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (367 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (367 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_367 :
    recurrence4Scalar1Left.coeff 367 =
      (((((19 * 10 ^ 70 +
        7336275690798807945599269190305428904004797835404189367305271988838503) * 10 ^ 70 +
        8741989554930283786392657351603025519575230724431383274503286923079820) * 10 ^ 70 +
        2802369499066589427466513298936511507868580259595788215871963328752084) * 10 ^ 70 +
        0644222007873088859592204207811773614894422035530570831033817477871954) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (367 - x)) = _
  rw [show 368 = 177 +
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
    rw [show 63 = 24 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (368 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (368 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (368 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_368 :
    recurrence4Scalar1Left.coeff 368 =
      -(((((9 * 10 ^ 70 +
        6465043000196833101638524330239864479766768207671266510395801052487523) * 10 ^ 70 +
        3761360259714485838332306918138413099587472761014650766202639963005127) * 10 ^ 70 +
        2838594862038518218738535975113015699004737080823063307020211020543760) * 10 ^ 70 +
        0370861328728594211005818480910128939754373468487102295575729516102141) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (368 - x)) = _
  rw [show 369 = 178 +
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
    rw [show 63 = 23 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (369 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (369 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (369 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_369 :
    recurrence4Scalar1Left.coeff 369 =
      (((((4 * 10 ^ 70 +
        5389401878868888227414780227184253382070741584795134157710049474816653) * 10 ^ 70 +
        1928043833073265087657853752866389282218341066489388010794865675287128) * 10 ^ 70 +
        2598793490802050409125458690862019509046199794408810721424568710058378) * 10 ^ 70 +
        6618617878232280657264859288218716680842946654166920191159499713367884) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (369 - x)) = _
  rw [show 370 = 179 +
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
    rw [show 63 = 22 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (370 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (370 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (370 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_370 :
    recurrence4Scalar1Left.coeff 370 =
      -(((((2 * 10 ^ 70 +
        0479733218762221458447180188128221889762229455988177374945681634988599) * 10 ^ 70 +
        7343267896931898430714429283376078668804392859571180372040668848072189) * 10 ^ 70 +
        2418620621461948136756500304630196610965698007171591761418423784788696) * 10 ^ 70 +
        7370229509365208150520678304248380806224991048329319980559809676390267) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (370 - x)) = _
  rw [show 371 = 180 +
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
    rw [show 63 = 21 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (371 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (371 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (371 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_371 :
    recurrence4Scalar1Left.coeff 371 =
      ((((8843006645530847008283591501381994255816421574603555224117913879215202 * 10 ^ 70 +
        9636131120485547244753483961918262721168067547225524532880930659226610) * 10 ^ 70 +
        8012860776328367651443428520480373108089372773896509990992763740177727) * 10 ^ 70 +
        0844914282464492881664292484368015765477574926469148255332622315101696) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (371 - x)) = _
  rw [show 372 = 181 +
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
    rw [show 63 = 20 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (372 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (372 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (372 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_372 :
    recurrence4Scalar1Left.coeff 372 =
      -((((3648382073412333222061561348652906840256521808867092491287770212749070 * 10 ^ 70 +
        7240413498609567050821700023362432779178341824701445608935046649377637) * 10 ^ 70 +
        5586701636989314276186645498549090123957202742767383381015591983536592) * 10 ^ 70 +
        4891286175216737993559677057345066343741104546926511948948937144546611) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (372 - x)) = _
  rw [show 373 = 182 +
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
    rw [show 63 = 19 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (373 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (373 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (373 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_373 :
    recurrence4Scalar1Left.coeff 373 =
      ((((1435361067908708978519196850778050859103179526633042196374572991383475 * 10 ^ 70 +
        8470723994943814647364911403169693295245344660306176237253268604766895) * 10 ^ 70 +
        3566002918688584564743675700297277429384642273002852269873417836730392) * 10 ^ 70 +
        1314461527100605539055434015342209642703763886775615503848465719335187) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (373 - x)) = _
  rw [show 374 = 183 +
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
    rw [show 63 = 18 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (374 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (374 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (374 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_374 :
    recurrence4Scalar1Left.coeff 374 =
      -((((536784570330817203783269972957417230245697976627476645565931969367078 * 10 ^ 70 +
        5350571527158693427593424886505071546125563152288390378816938253707857) * 10 ^ 70 +
        1385460374595518709148559526998680397926687702365799340621817638895141) * 10 ^ 70 +
        3826748285161867671589983929755363021271738758555721391840691888070940) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (374 - x)) = _
  rw [show 375 = 184 +
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
    rw [show 63 = 17 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (375 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (375 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (375 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_375 :
    recurrence4Scalar1Left.coeff 375 =
      ((((189793332144890435190517802965787706757234988976009536977860560593633 * 10 ^ 70 +
        8017998170692158779341176962781789707305335671078780376434657519894958) * 10 ^ 70 +
        3486344398812608423256787257906251838188553179460854119967674293196670) * 10 ^ 70 +
        8165234753002904511137324815335811951801777863260907092789586762632005) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (375 - x)) = _
  rw [show 376 = 185 +
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
    rw [show 63 = 16 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (376 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (376 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (376 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_376 :
    recurrence4Scalar1Left.coeff 376 =
      -((((62854138855448405342118671084633626610654951268749638312312524898154 * 10 ^ 70 +
        7815946378458163527052963659437132901315476230760947871183191329877763) * 10 ^ 70 +
        9376289580230863958256638946437135427206097973769861535385937327969902) * 10 ^ 70 +
        2532164795404017709461322435853553916236266707364159162334449599573608) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (376 - x)) = _
  rw [show 377 = 186 +
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
    rw [show 63 = 15 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (377 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (377 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (377 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_377 :
    recurrence4Scalar1Left.coeff 377 =
      ((((19160771257707081781073292680202174845763607484571715127607680662851 * 10 ^ 70 +
        8157120390339633258717415796223669776706272047452964839076459144360447) * 10 ^ 70 +
        5781648981856297595764885333483262565403136559220271211981661493914946) * 10 ^ 70 +
        4649280921232186415501905639390271782096058074411047213253144588036517) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (377 - x)) = _
  rw [show 378 = 187 +
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
    rw [show 63 = 14 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
