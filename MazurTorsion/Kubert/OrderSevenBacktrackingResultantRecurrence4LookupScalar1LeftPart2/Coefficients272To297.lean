/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
