/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart2Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A0_coeff_1
  recurrence4A0_coeff_10
  recurrence4A0_coeff_100
  recurrence4A0_coeff_101
  recurrence4A0_coeff_102
  recurrence4A0_coeff_103
  recurrence4A0_coeff_104
  recurrence4A0_coeff_105
  recurrence4A0_coeff_106
  recurrence4A0_coeff_107
  recurrence4A0_coeff_108
  recurrence4A0_coeff_109
  recurrence4A0_coeff_11
  recurrence4A0_coeff_110
  recurrence4A0_coeff_111
  recurrence4A0_coeff_112
  recurrence4A0_coeff_113
  recurrence4A0_coeff_114
  recurrence4A0_coeff_115
  recurrence4A0_coeff_116
  recurrence4A0_coeff_117
  recurrence4A0_coeff_118
  recurrence4A0_coeff_119
  recurrence4A0_coeff_12
  recurrence4A0_coeff_120
  recurrence4A0_coeff_121
  recurrence4A0_coeff_122
  recurrence4A0_coeff_123
  recurrence4A0_coeff_124
  recurrence4A0_coeff_125
  recurrence4A0_coeff_126
  recurrence4A0_coeff_127
  recurrence4A0_coeff_128
  recurrence4A0_coeff_129
  recurrence4A0_coeff_13
  recurrence4A0_coeff_130
  recurrence4A0_coeff_131
  recurrence4A0_coeff_132
  recurrence4A0_coeff_133
  recurrence4A0_coeff_134
  recurrence4A0_coeff_135
  recurrence4A0_coeff_136
  recurrence4A0_coeff_137
  recurrence4A0_coeff_138
  recurrence4A0_coeff_139
  recurrence4A0_coeff_14
  recurrence4A0_coeff_140
  recurrence4A0_coeff_141
  recurrence4A0_coeff_142
  recurrence4A0_coeff_143
  recurrence4A0_coeff_144
  recurrence4A0_coeff_145
  recurrence4A0_coeff_146
  recurrence4A0_coeff_147
  recurrence4A0_coeff_148
  recurrence4A0_coeff_149
  recurrence4A0_coeff_15
  recurrence4A0_coeff_150
  recurrence4A0_coeff_151
  recurrence4A0_coeff_152
  recurrence4A0_coeff_153
  recurrence4A0_coeff_154
  recurrence4A0_coeff_155
  recurrence4A0_coeff_156

attribute [local simp]
  recurrence4A0_coeff_157
  recurrence4A0_coeff_158
  recurrence4A0_coeff_159
  recurrence4A0_coeff_16
  recurrence4A0_coeff_160
  recurrence4A0_coeff_161
  recurrence4A0_coeff_162
  recurrence4A0_coeff_163
  recurrence4A0_coeff_164
  recurrence4A0_coeff_165
  recurrence4A0_coeff_166
  recurrence4A0_coeff_167
  recurrence4A0_coeff_168
  recurrence4A0_coeff_169
  recurrence4A0_coeff_17
  recurrence4A0_coeff_170
  recurrence4A0_coeff_171
  recurrence4A0_coeff_172
  recurrence4A0_coeff_173
  recurrence4A0_coeff_174
  recurrence4A0_coeff_175
  recurrence4A0_coeff_176
  recurrence4A0_coeff_177
  recurrence4A0_coeff_178
  recurrence4A0_coeff_179
  recurrence4A0_coeff_18
  recurrence4A0_coeff_180
  recurrence4A0_coeff_181
  recurrence4A0_coeff_182
  recurrence4A0_coeff_183
  recurrence4A0_coeff_184
  recurrence4A0_coeff_185
  recurrence4A0_coeff_186
  recurrence4A0_coeff_187
  recurrence4A0_coeff_188
  recurrence4A0_coeff_189
  recurrence4A0_coeff_19
  recurrence4A0_coeff_190
  recurrence4A0_coeff_191
  recurrence4A0_coeff_192
  recurrence4A0_coeff_193
  recurrence4A0_coeff_194
  recurrence4A0_coeff_2
  recurrence4A0_coeff_20
  recurrence4A0_coeff_21
  recurrence4A0_coeff_22
  recurrence4A0_coeff_23
  recurrence4A0_coeff_24
  recurrence4A0_coeff_25
  recurrence4A0_coeff_26
  recurrence4A0_coeff_27
  recurrence4A0_coeff_28
  recurrence4A0_coeff_29
  recurrence4A0_coeff_3
  recurrence4A0_coeff_30
  recurrence4A0_coeff_31
  recurrence4A0_coeff_32
  recurrence4A0_coeff_33
  recurrence4A0_coeff_34
  recurrence4A0_coeff_35
  recurrence4A0_coeff_36
  recurrence4A0_coeff_37
  recurrence4A0_coeff_38
  recurrence4A0_coeff_39

attribute [local simp]
  recurrence4A0_coeff_4
  recurrence4A0_coeff_40
  recurrence4A0_coeff_41
  recurrence4A0_coeff_42
  recurrence4A0_coeff_43
  recurrence4A0_coeff_44
  recurrence4A0_coeff_45
  recurrence4A0_coeff_46
  recurrence4A0_coeff_47
  recurrence4A0_coeff_48
  recurrence4A0_coeff_49
  recurrence4A0_coeff_5
  recurrence4A0_coeff_50
  recurrence4A0_coeff_51
  recurrence4A0_coeff_52
  recurrence4A0_coeff_53
  recurrence4A0_coeff_54
  recurrence4A0_coeff_55
  recurrence4A0_coeff_56
  recurrence4A0_coeff_57
  recurrence4A0_coeff_58
  recurrence4A0_coeff_59
  recurrence4A0_coeff_6
  recurrence4A0_coeff_60
  recurrence4A0_coeff_61
  recurrence4A0_coeff_62
  recurrence4A0_coeff_63
  recurrence4A0_coeff_64
  recurrence4A0_coeff_65
  recurrence4A0_coeff_66
  recurrence4A0_coeff_67
  recurrence4A0_coeff_68
  recurrence4A0_coeff_69
  recurrence4A0_coeff_7
  recurrence4A0_coeff_70
  recurrence4A0_coeff_71
  recurrence4A0_coeff_72
  recurrence4A0_coeff_73
  recurrence4A0_coeff_74
  recurrence4A0_coeff_75
  recurrence4A0_coeff_76
  recurrence4A0_coeff_77
  recurrence4A0_coeff_78
  recurrence4A0_coeff_79
  recurrence4A0_coeff_8
  recurrence4A0_coeff_80
  recurrence4A0_coeff_81
  recurrence4A0_coeff_82
  recurrence4A0_coeff_83
  recurrence4A0_coeff_84
  recurrence4A0_coeff_85
  recurrence4A0_coeff_86
  recurrence4A0_coeff_87
  recurrence4A0_coeff_88
  recurrence4A0_coeff_89
  recurrence4A0_coeff_9
  recurrence4A0_coeff_90
  recurrence4A0_coeff_91
  recurrence4A0_coeff_92
  recurrence4A0_coeff_93
  recurrence4A0_coeff_94
  recurrence4A0_coeff_95
  recurrence4A0_coeff_96
  recurrence4A0_coeff_97

attribute [local simp]
  recurrence4A0_coeff_98
  recurrence4A0_coeff_99
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_162
  recurrence4LeadingSquare_coeff_163
  recurrence4LeadingSquare_coeff_164
  recurrence4LeadingSquare_coeff_165
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_226
  recurrence4LeadingSquare_coeff_227
  recurrence4LeadingSquare_coeff_228
  recurrence4LeadingSquare_coeff_229
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_290
  recurrence4LeadingSquare_coeff_291
  recurrence4LeadingSquare_coeff_292
  recurrence4LeadingSquare_coeff_293
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

private theorem recurrence4Scalar0Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (294 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (294 + x) *
        remainder4Coefficient0.coeff (294 - (294 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 294 + x
  · rw [recurrence4LeadingSquare_coeff_high (294 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (294 - (294 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_294 :
    recurrence4Scalar0Left.coeff 294 =
      (((((16497899138550805261824915 * 10 ^ 70 +
        3297402351679255855698781746235564982327274220961718093979793521424217) * 10 ^ 70 +
        1768039967636250658522664280582632538317029585512224364291500015353811) * 10 ^ 70 +
        4655501458629432374181708817102183720135228280596257978524947137390895) * 10 ^ 70 +
        0220403045316459890984993238597879342288181171837699743758325354464135) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 295,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (294 - x)) = _
  rw [show 295 = 100 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (295 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (295 + x) *
        remainder4Coefficient0.coeff (295 - (295 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 295 + x
  · rw [recurrence4LeadingSquare_coeff_high (295 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (295 - (295 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_295 :
    recurrence4Scalar0Left.coeff 295 =
      -(((((11047972745638533024990341 * 10 ^ 70 +
        6879200328617855031820553390026438362566735982597368593716631262854488) * 10 ^ 70 +
        5220242582349312662011609521759332305822708565463467953438989877634075) * 10 ^ 70 +
        3230731943147417741748569090011561935938791885853606333632224654406434) * 10 ^ 70 +
        5362671574282679526076246977099696751551133183671194827747953371036713) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 296,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (295 - x)) = _
  rw [show 296 = 101 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (296 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (296 + x) *
        remainder4Coefficient0.coeff (296 - (296 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 296 + x
  · rw [recurrence4LeadingSquare_coeff_high (296 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (296 - (296 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_296 :
    recurrence4Scalar0Left.coeff 296 =
      (((((7246604950908926593887856 * 10 ^ 70 +
        4939316942553517775809132202992790928786387006304879630654920020952845) * 10 ^ 70 +
        1017848317478754417631670718837828677389307110869689491205846720323179) * 10 ^ 70 +
        6911902613443042936820105401983619675200274860697756928651256911765639) * 10 ^ 70 +
        1291568249470995782020702878504828393419024057873875258623863337267487) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 297,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (296 - x)) = _
  rw [show 297 = 102 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (297 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (297 + x) *
        remainder4Coefficient0.coeff (297 - (297 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 297 + x
  · rw [recurrence4LeadingSquare_coeff_high (297 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (297 - (297 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_297 :
    recurrence4Scalar0Left.coeff 297 =
      -(((((4652860976739064663588479 * 10 ^ 70 +
        4592066352103156477901803661911050005784707288457405998370251892048286) * 10 ^ 70 +
        3454928738728223327862420444773793955933837275761172798964086853114437) * 10 ^ 70 +
        4866152881913102856586242807807343850621140679722680450412801937247204) * 10 ^ 70 +
        9819596260952149688147461425972166423408546837414296803644679475461681) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 298,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (297 - x)) = _
  rw [show 298 = 103 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (298 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (298 + x) *
        remainder4Coefficient0.coeff (298 - (298 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 298 + x
  · rw [recurrence4LeadingSquare_coeff_high (298 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (298 - (298 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_298 :
    recurrence4Scalar0Left.coeff 298 =
      (((((2921742518873368599346554 * 10 ^ 70 +
        6947627956325718788972864577266062100429341370251376367952423761046507) * 10 ^ 70 +
        2321854509654193560301431782200812803987462394479088401734761620902555) * 10 ^ 70 +
        0475013340823085133025003518975726301166927187620638100514928957807249) * 10 ^ 70 +
        6046879887427581572036111291614998359264780659266852977170983475479455) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 299,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (298 - x)) = _
  rw [show 299 = 104 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (299 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (299 + x) *
        remainder4Coefficient0.coeff (299 - (299 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 299 + x
  · rw [recurrence4LeadingSquare_coeff_high (299 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (299 - (299 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_299 :
    recurrence4Scalar0Left.coeff 299 =
      -(((((1791958838712813718463075 * 10 ^ 70 +
        2265838665915451804117859136907342416050679211981992619406347950174241) * 10 ^ 70 +
        6031113453252300329139051139762403864567182418862406765673018346800634) * 10 ^ 70 +
        3315237541864044949334856080254696221777182640640533706438215636645166) * 10 ^ 70 +
        9712648654374854746251207928562472623881636123523977421014320274932261) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 300,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (299 - x)) = _
  rw [show 300 = 105 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (300 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (300 + x) *
        remainder4Coefficient0.coeff (300 - (300 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 300 + x
  · rw [recurrence4LeadingSquare_coeff_high (300 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (300 - (300 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_300 :
    recurrence4Scalar0Left.coeff 300 =
      (((((1071426368013068493702595 * 10 ^ 70 +
        5084217754784976691159171845601353167712261643563674048458818244123542) * 10 ^ 70 +
        7328600178277211809038249838845384009419741624122314799900937082529487) * 10 ^ 70 +
        0781905438629513441654674144410902457586305817729079836182969165291640) * 10 ^ 70 +
        7461159055158607779181091928009031753473414748607473370994497513322730) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 301,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (300 - x)) = _
  rw [show 301 = 106 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (301 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (301 + x) *
        remainder4Coefficient0.coeff (301 - (301 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 301 + x
  · rw [recurrence4LeadingSquare_coeff_high (301 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (301 - (301 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_301 :
    recurrence4Scalar0Left.coeff 301 =
      -(((((622831205397898523188403 * 10 ^ 70 +
        0475725565543262174377447342393871413996000765173214431276888314569759) * 10 ^ 70 +
        6871515569732321203721603833642439670797405909740683232393595474278634) * 10 ^ 70 +
        3987689572291781202378899540513579283710369605183108459268530437320372) * 10 ^ 70 +
        4635440144207683185816805237733875777034339139973381426154647649779187) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 302,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (301 - x)) = _
  rw [show 302 = 107 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (302 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (302 + x) *
        remainder4Coefficient0.coeff (302 - (302 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 302 + x
  · rw [recurrence4LeadingSquare_coeff_high (302 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (302 - (302 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_302 :
    recurrence4Scalar0Left.coeff 302 =
      (((((350606070223201710030992 * 10 ^ 70 +
        0074727351165544226467146705052889981138947664247734451998037690161094) * 10 ^ 70 +
        1155939439052154913543111375902730094223425552771396353897959401463857) * 10 ^ 70 +
        4034552259944450950834482124862535527167232877158068140575056204470834) * 10 ^ 70 +
        4234656943614899789668237942578221736893297184403259052957668996827783) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 303,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (302 - x)) = _
  rw [show 303 = 108 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (303 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (303 + x) *
        remainder4Coefficient0.coeff (303 - (303 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 303 + x
  · rw [recurrence4LeadingSquare_coeff_high (303 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (303 - (303 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_303 :
    recurrence4Scalar0Left.coeff 303 =
      -(((((189953342761444793806226 * 10 ^ 70 +
        4882139019035597655626507010440854512692046322453669840803499591845361) * 10 ^ 70 +
        6232190407953685362630916205859126395749383500602621305376519208918262) * 10 ^ 70 +
        2268456441184211107176359068369037616315310052319156010841842350793420) * 10 ^ 70 +
        8020091691963044365967715484356298708304938416646332887951523653825608) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 304,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (303 - x)) = _
  rw [show 304 = 109 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (304 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (304 + x) *
        remainder4Coefficient0.coeff (304 - (304 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 304 + x
  · rw [recurrence4LeadingSquare_coeff_high (304 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (304 - (304 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_304 :
    recurrence4Scalar0Left.coeff 304 =
      (((((98062775207008569170814 * 10 ^ 70 +
        1407587388356572512069048216634665341836038459072622049022978709610036) * 10 ^ 70 +
        7825427908947077530537637549789590333066433963559219721315688514811740) * 10 ^ 70 +
        6033439844605559114690376712985979023274223460581936066536840883848932) * 10 ^ 70 +
        0748468005432503810666787049079305885682649387021596979234638290081567) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 305,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (304 - x)) = _
  rw [show 305 = 110 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (305 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (305 + x) *
        remainder4Coefficient0.coeff (305 - (305 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 305 + x
  · rw [recurrence4LeadingSquare_coeff_high (305 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (305 - (305 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_305 :
    recurrence4Scalar0Left.coeff 305 =
      -(((((47381930995197572019851 * 10 ^ 70 +
        0514266360010231984069498448363938381605884704752118293609908696970369) * 10 ^ 70 +
        2910638113221676929108174726371816414610319020258018088657706692605909) * 10 ^ 70 +
        4435716145070530758246109158937469602097825077058991174785810336004126) * 10 ^ 70 +
        0389919367742727680046504306554123376386651755457958876283021002958287) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 306,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (305 - x)) = _
  rw [show 306 = 111 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (306 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (306 + x) *
        remainder4Coefficient0.coeff (306 - (306 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 306 + x
  · rw [recurrence4LeadingSquare_coeff_high (306 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (306 - (306 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_306 :
    recurrence4Scalar0Left.coeff 306 =
      (((((20650091016895952149621 * 10 ^ 70 +
        7773310680564450231763462130246057762117828874722815425764732004108400) * 10 ^ 70 +
        0340592041877041280044420210614143984374240477806069968444383402875407) * 10 ^ 70 +
        5768165320613077899946294215642217634644896125751252788566292446777428) * 10 ^ 70 +
        5680828180984308932576660445128172784453623802273826153814501994619657) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 307,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (306 - x)) = _
  rw [show 307 = 112 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (307 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (307 + x) *
        remainder4Coefficient0.coeff (307 - (307 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 307 + x
  · rw [recurrence4LeadingSquare_coeff_high (307 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (307 - (307 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_307 :
    recurrence4Scalar0Left.coeff 307 =
      -(((((7356542555455141946226 * 10 ^ 70 +
        6057240005156943344503846234612874638548357728794556641037174662614408) * 10 ^ 70 +
        2361239552539525292701772879593241353154614260752201644440941239572178) * 10 ^ 70 +
        9459972988326855612881478393123853274778865200107472144276017630273599) * 10 ^ 70 +
        8545409175674305005224394537416539848991786853626884589444050360513711) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 308,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (307 - x)) = _
  rw [show 308 = 113 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (308 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (308 + x) *
        remainder4Coefficient0.coeff (308 - (308 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 308 + x
  · rw [recurrence4LeadingSquare_coeff_high (308 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (308 - (308 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_308 :
    recurrence4Scalar0Left.coeff 308 =
      (((((1294144066977620120302 * 10 ^ 70 +
        4133327963853956487756495255875593800127256122810374090607861463861179) * 10 ^ 70 +
        4243567899701663745131823730106842908425593281596020538837555482393909) * 10 ^ 70 +
        3405384376754300418804297744430917338120632479752081460391745974288593) * 10 ^ 70 +
        7333630934623147508582858821671938987659609082020348884439424922767049) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 309,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (308 - x)) = _
  rw [show 309 = 114 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (309 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (309 + x) *
        remainder4Coefficient0.coeff (309 - (309 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 309 + x
  · rw [recurrence4LeadingSquare_coeff_high (309 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (309 - (309 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_309 :
    recurrence4Scalar0Left.coeff 309 =
      (((((1079436763579607541378 * 10 ^ 70 +
        7439579287215822056702247808432588831062093030375401510976491871640563) * 10 ^ 70 +
        0920377085234568986314506402941618860474559059881281963603090675450584) * 10 ^ 70 +
        9603232038282923168650207294113873366004175016906728728610376469332185) * 10 ^ 70 +
        7165319261703855308712431900141471250030223210967629847858527400936477) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 310,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (309 - x)) = _
  rw [show 310 = 115 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (310 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (310 + x) *
        remainder4Coefficient0.coeff (310 - (310 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 310 + x
  · rw [recurrence4LeadingSquare_coeff_high (310 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (310 - (310 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_310 :
    recurrence4Scalar0Left.coeff 310 =
      -(((((1706741616865847833002 * 10 ^ 70 +
        3103700822541951619628851311418018124899763704618449640426774362893552) * 10 ^ 70 +
        9110755942617648577636605404080343738141730522305693498212316742310061) * 10 ^ 70 +
        1456160917400346504115915774364889949745785096053959480792932576696795) * 10 ^ 70 +
        0192713038786467717895544408772080176160398137618758427121916064072217) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 311,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (310 - x)) = _
  rw [show 311 = 116 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (311 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (311 + x) *
        remainder4Coefficient0.coeff (311 - (311 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 311 + x
  · rw [recurrence4LeadingSquare_coeff_high (311 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (311 - (311 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_311 :
    recurrence4Scalar0Left.coeff 311 =
      (((((1601840006842740569914 * 10 ^ 70 +
        8354426259600073105759029194368940883288803638128415697337458020148352) * 10 ^ 70 +
        6619030334546499384564994630867318564347749052211336104820400434115121) * 10 ^ 70 +
        6464965770890861606028020646512199828411800201645859422271537322706044) * 10 ^ 70 +
        9333176375690059617767814803954895462516423564939199200395232720816419) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 312,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (311 - x)) = _
  rw [show 312 = 117 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (312 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (312 + x) *
        remainder4Coefficient0.coeff (312 - (312 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 312 + x
  · rw [recurrence4LeadingSquare_coeff_high (312 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (312 - (312 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_312 :
    recurrence4Scalar0Left.coeff 312 =
      -(((((1260285424467334044443 * 10 ^ 70 +
        5849139159842855180433829458273551327228779289413232843324815985706725) * 10 ^ 70 +
        7101744375692449001020276717818266298166023874058572237229666145651186) * 10 ^ 70 +
        7373137827447356714434675714485224574013477441292931766976832217373314) * 10 ^ 70 +
        3057614941670964472771270621774523006213105316032376160045476212825426) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 313,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (312 - x)) = _
  rw [show 313 = 118 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (313 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (313 + x) *
        remainder4Coefficient0.coeff (313 - (313 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 313 + x
  · rw [recurrence4LeadingSquare_coeff_high (313 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (313 - (313 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_313 :
    recurrence4Scalar0Left.coeff 313 =
      (((((901120777247119908456 * 10 ^ 70 +
        0004201764020387499328849059937476865950646382191312284851893292179111) * 10 ^ 70 +
        5419534312424391204473918775171565121111684452520021817305854236029082) * 10 ^ 70 +
        0821488405446920091314114579669201165151224377443860470333653316671443) * 10 ^ 70 +
        8632029692482919554219109345644484140549423992474604726398925938270870) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 314,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (313 - x)) = _
  rw [show 314 = 119 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (314 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (314 + x) *
        remainder4Coefficient0.coeff (314 - (314 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 314 + x
  · rw [recurrence4LeadingSquare_coeff_high (314 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (314 - (314 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_314 :
    recurrence4Scalar0Left.coeff 314 =
      -(((((604459489676475061250 * 10 ^ 70 +
        6889815953873099531780813115931409551038283967890931157361714736457021) * 10 ^ 70 +
        8372719197888357787674134551003341748602163872809034562929502870015087) * 10 ^ 70 +
        1161168286750204815513652809646154760423105401638719796615044789781062) * 10 ^ 70 +
        3620854674822507127493123139284649614199100897765239240131600184681712) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 315,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (314 - x)) = _
  rw [show 315 = 120 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (315 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (315 + x) *
        remainder4Coefficient0.coeff (315 - (315 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 315 + x
  · rw [recurrence4LeadingSquare_coeff_high (315 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (315 - (315 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_315 :
    recurrence4Scalar0Left.coeff 315 =
      (((((386339429827012109196 * 10 ^ 70 +
        1676221583108625800173053679564540514078799611666493421099721703103655) * 10 ^ 70 +
        7653848594952677277322425611024861578026294153994262120042770954813621) * 10 ^ 70 +
        7217792892591656832698227490075658976739890679289983668521174266604931) * 10 ^ 70 +
        5540349388390043208210537672403332732226222693728867445097643749686616) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 316,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (315 - x)) = _
  rw [show 316 = 121 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (316 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (316 + x) *
        remainder4Coefficient0.coeff (316 - (316 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 316 + x
  · rw [recurrence4LeadingSquare_coeff_high (316 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (316 - (316 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_316 :
    recurrence4Scalar0Left.coeff 316 =
      -(((((237279127513408087564 * 10 ^ 70 +
        8128819126499599731370244859126603993693682376494814302031229246931512) * 10 ^ 70 +
        2936421156911464485082352789491630237702313801784746080526048580207691) * 10 ^ 70 +
        5948867209890395641385217682173210192442287265215776454522481696836339) * 10 ^ 70 +
        3417967543084476121950235443056835441225257018278496895279388584189439) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 317,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (316 - x)) = _
  rw [show 317 = 122 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (317 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (317 + x) *
        remainder4Coefficient0.coeff (317 - (317 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 317 + x
  · rw [recurrence4LeadingSquare_coeff_high (317 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (317 - (317 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_317 :
    recurrence4Scalar0Left.coeff 317 =
      (((((140702692186626200218 * 10 ^ 70 +
        4336092021099237866610518377063306291654540347813270783665362380207690) * 10 ^ 70 +
        7090059775494084386240294795701252163484598144980538353801170336862850) * 10 ^ 70 +
        2972443802975218317938506856763886724241487009987683095698255219499774) * 10 ^ 70 +
        5880262719830520744315073294675484852042351830851623072625219839179029) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 318,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (317 - x)) = _
  rw [show 318 = 123 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (318 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (318 + x) *
        remainder4Coefficient0.coeff (318 - (318 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 318 + x
  · rw [recurrence4LeadingSquare_coeff_high (318 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (318 - (318 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_318 :
    recurrence4Scalar0Left.coeff 318 =
      -(((((80756852964960566310 * 10 ^ 70 +
        7479700885271767310521422804013785291615342482860744242668723900010312) * 10 ^ 70 +
        3603843312663939330732312701890575465067861311401223849712030501772113) * 10 ^ 70 +
        3543102955548877224667961792382451611654775761995690804404132579633674) * 10 ^ 70 +
        4252547311832524401681082553489577190806488210190691444984920650533664) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 319,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (318 - x)) = _
  rw [show 319 = 124 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
