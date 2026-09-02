/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart3Simp
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
  recurrence4A1_coeff_150
  recurrence4A1_coeff_151
  recurrence4A1_coeff_152
  recurrence4A1_coeff_153
  recurrence4A1_coeff_154
  recurrence4A1_coeff_155
  recurrence4A1_coeff_156
  recurrence4A1_coeff_157
  recurrence4A1_coeff_158
  recurrence4A1_coeff_159
  recurrence4A1_coeff_160
  recurrence4A1_coeff_161
  recurrence4A1_coeff_162
  recurrence4A1_coeff_163

attribute [local simp]
  recurrence4A1_coeff_164
  recurrence4A1_coeff_165
  recurrence4A1_coeff_166
  recurrence4A1_coeff_167
  recurrence4A1_coeff_168
  recurrence4A1_coeff_169
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
  recurrence4A1_coeff_190
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
  recurrence4A1_coeff_80
  recurrence4A1_coeff_81
  recurrence4A1_coeff_82
  recurrence4A1_coeff_83
  recurrence4A1_coeff_84
  recurrence4A1_coeff_85
  recurrence4A1_coeff_86

attribute [local simp]
  recurrence4A1_coeff_87
  recurrence4A1_coeff_88
  recurrence4A1_coeff_89
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
  recurrence4LeadingSquare_coeff_233
  recurrence4LeadingSquare_coeff_234
  recurrence4LeadingSquare_coeff_235
  recurrence4LeadingSquare_coeff_236
  recurrence4LeadingSquare_coeff_237
  recurrence4LeadingSquare_coeff_238

attribute [local simp]
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
  recurrence4LeadingSquare_coeff_297
  recurrence4LeadingSquare_coeff_298
  recurrence4LeadingSquare_coeff_299
  recurrence4LeadingSquare_coeff_300
  recurrence4LeadingSquare_coeff_301
  recurrence4LeadingSquare_coeff_302

attribute [local simp]
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

private theorem recurrence4Scalar1Left_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (402 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (402 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (402 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_402 :
    recurrence4Scalar1Left.coeff 402 =
      -((((98917408296810271292170158808917936167325896172452075238 * 10 ^ 70 +
        9169418257578094511175341965660512776544462122859079807439191400257008) * 10 ^ 70 +
        5400387037596255149655546111624879898995381343463200222585982850039105) * 10 ^ 70 +
        4353881076843710411188718031963635799294629020482387471015307450565664) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (402 - x)) = _
  rw [show 403 = 212 +
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
    rw [show 95 = 21 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_402_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (403 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (403 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (403 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_403 :
    recurrence4Scalar1Left.coeff 403 =
      ((((25846881918653240098034177302852290182952481196438292163 * 10 ^ 70 +
        2570225796188144464798417345153265864641008668365226429169773339511799) * 10 ^ 70 +
        2154737625335994079643359869028001379978071241056494024315293872235177) * 10 ^ 70 +
        7131615875789113140133482786878238086467096229178946221832342698348831) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (403 - x)) = _
  rw [show 404 = 213 +
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
    rw [show 95 = 20 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_403_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (404 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (404 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (404 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_404 :
    recurrence4Scalar1Left.coeff 404 =
      -((((5740402188605195907472400344130340770211200135599075651 * 10 ^ 70 +
        0560003251999741123666681771231998711188719219727411244286395820992567) * 10 ^ 70 +
        2190573122789264921647764864345487586590772584428097401730498778034083) * 10 ^ 70 +
        9196843614328480620238869185752761695960025562418982160072582381567167) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (404 - x)) = _
  rw [show 405 = 214 +
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
    rw [show 95 = 19 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_404_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (405 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (405 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (405 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_405 :
    recurrence4Scalar1Left.coeff 405 =
      ((((862872694813203644206140148585639008528870726707884809 * 10 ^ 70 +
        8967064915181247241662684393189569207362875732855764767650662915568811) * 10 ^ 70 +
        3102163939232872677796778228325135324240118042485581256164447411617729) * 10 ^ 70 +
        9744257686529476786317350356872136002415883727270756313708784115368614) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (405 - x)) = _
  rw [show 406 = 215 +
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
    rw [show 95 = 18 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_405_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (406 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (406 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (406 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_406 :
    recurrence4Scalar1Left.coeff 406 =
      ((((64580528461842676327668427939213690958491912497404247 * 10 ^ 70 +
        5140426344799803355782779423849857514325572779137368147986789576850114) * 10 ^ 70 +
        2995395822250643736005192863973284563014217279761447828018657773962184) * 10 ^ 70 +
        5562824849090928545524406498265953089816634592560704181718331386290243) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (406 - x)) = _
  rw [show 407 = 216 +
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
    rw [show 95 = 17 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_406_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (407 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (407 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_407 :
    recurrence4Scalar1Left.coeff 407 =
      -((((129855082238557060531636140453726928486478398458326952 * 10 ^ 70 +
        0072211381698904914286665233272197993204202892821685277573499322148915) * 10 ^ 70 +
        9568046203136006468050496109477719390064035799037448565463452603325588) * 10 ^ 70 +
        6897678354882317782781371900463215928124531984314749904438120767317417) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (407 - x)) = _
  rw [show 408 = 217 +
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
    rw [show 95 = 16 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (408 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (408 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_408 :
    recurrence4Scalar1Left.coeff 408 =
      ((((73459474923106570375205302864195010801279789206854839 * 10 ^ 70 +
        6018836374486327695723341164531081636783691662559399068766588647134660) * 10 ^ 70 +
        7089682455127297177757354634919546782462683144628031349405279296747534) * 10 ^ 70 +
        1097128352039454060058962586724668040157171994372766447361314277541714) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (408 - x)) = _
  rw [show 409 = 218 +
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
    rw [show 95 = 15 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (409 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (409 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_409 :
    recurrence4Scalar1Left.coeff 409 =
      -((((31820808060979318536141641939563337208727640615542154 * 10 ^ 70 +
        4037147711301805069834593766475507552469801309177756450023727502243082) * 10 ^ 70 +
        6392356130604645363001636207816250350088262745977487867771263165615839) * 10 ^ 70 +
        3024993965341673086180955474982614459861939201039729347983884631501576) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (409 - x)) = _
  rw [show 410 = 219 +
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
    rw [show 95 = 14 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (410 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (410 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_410 :
    recurrence4Scalar1Left.coeff 410 =
      ((((11994358246079443290585941401826812595140920859566178 * 10 ^ 70 +
        9683890495452234652004104537769374887298675975130935985560637713488089) * 10 ^ 70 +
        2396486437086105963064866308802806266118950030216728262747177089172581) * 10 ^ 70 +
        3189819720392827392440320705534111116112038916802652886666450741164327) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (410 - x)) = _
  rw [show 411 = 220 +
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
    rw [show 95 = 13 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (411 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (411 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_411 :
    recurrence4Scalar1Left.coeff 411 =
      -((((4093671763381681896092051416408173094667996093033718 * 10 ^ 70 +
        5018460905050237008100748920873282186447989251926484817135527037917295) * 10 ^ 70 +
        7845514590531867474283596776966287501163374743623457848581552618040595) * 10 ^ 70 +
        4970592591284959260482848793370107295676550505828338598423548382496355) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (411 - x)) = _
  rw [show 412 = 221 +
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
    rw [show 95 = 12 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (412 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (412 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_412 :
    recurrence4Scalar1Left.coeff 412 =
      ((((1279919271796075695545371370259381360927466363969625 * 10 ^ 70 +
        9395963517978325275154296671380923570840430305438325485349175070209183) * 10 ^ 70 +
        0551724092038884498873180375015260763465414168392786190696355232625318) * 10 ^ 70 +
        9745357993942996022285614724118974824881865326959549056619899874358434) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (412 - x)) = _
  rw [show 413 = 222 +
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
    rw [show 95 = 11 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (413 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (413 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_413 :
    recurrence4Scalar1Left.coeff 413 =
      -((((364240652672719534656407688975153628253462084434102 * 10 ^ 70 +
        3419985171278512717081510964126738033519701850532104384619071642234280) * 10 ^ 70 +
        5484733120762020260584673016102477110082918827475485063668918854304877) * 10 ^ 70 +
        4107391998202213521235144502197855630197551440930291305605238757127339) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (413 - x)) = _
  rw [show 414 = 223 +
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
    rw [show 95 = 10 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (414 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (414 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_414 :
    recurrence4Scalar1Left.coeff 414 =
      ((((91321664644834798443420472916971665488340525665319 * 10 ^ 70 +
        6869021028907105602022973209332927536952039587201809480726558936793727) * 10 ^ 70 +
        7712521298751055130823100930486599751324285228301730376102860924059763) * 10 ^ 70 +
        7444773667273925475485147299406743971451332504838440215527581783518564) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (414 - x)) = _
  rw [show 415 = 224 +
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
    rw [show 95 = 9 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (415 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (415 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_415 :
    recurrence4Scalar1Left.coeff 415 =
      -((((18093747532835580094931853914879635823519590959047 * 10 ^ 70 +
        5299912497583999877128029133569553890273620795871722117037577042383698) * 10 ^ 70 +
        0943471285750363489270191334550555451627419500664566414032817088979510) * 10 ^ 70 +
        8342558641568778314270571948923146307134734783467450079207590644915365) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (415 - x)) = _
  rw [show 416 = 225 +
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
    rw [show 95 = 8 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (416 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (416 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_416 :
    recurrence4Scalar1Left.coeff 416 =
      ((((1406482427381880496917275668061640484620845854284 * 10 ^ 70 +
        3535156518383724821813346622282727829912979021605441814269171835531793) * 10 ^ 70 +
        3238688166584019888775097379902988964555717422853434906107629574176032) * 10 ^ 70 +
        4634937818662564289236177718066929197338073127047772509985006751798255) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (416 - x)) = _
  rw [show 417 = 226 +
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
    rw [show 95 = 7 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (417 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (417 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_417 :
    recurrence4Scalar1Left.coeff 417 =
      ((((1157762835744256948124674258530090550893825979758 * 10 ^ 70 +
        8544841375731930974319139188316223435000188492297111112828735019133558) * 10 ^ 70 +
        9737357803721534270173124970375218362946650720851294873397102512236948) * 10 ^ 70 +
        4840709909838745138023788703667819298184673173200706981795682795143364) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (417 - x)) = _
  rw [show 418 = 227 +
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
    rw [show 95 = 6 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (418 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (418 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_418 :
    recurrence4Scalar1Left.coeff 418 =
      -((((929318956110608539262677086872859490775358433728 * 10 ^ 70 +
        9223945280735823351859086278314892771964068651413934522587902823358253) * 10 ^ 70 +
        1620181821801449622014932646703778525066809965184897832096785347938424) * 10 ^ 70 +
        1149804731049418471702505947825838553536102874738345108587247150229125) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (418 - x)) = _
  rw [show 419 = 228 +
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
    rw [show 95 = 5 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (419 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (419 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_419 :
    recurrence4Scalar1Left.coeff 419 =
      ((((482532798387741048559158022224549802066621763098 * 10 ^ 70 +
        2018085154093259519784368587024677217731071925777641137935506559804199) * 10 ^ 70 +
        3656206730775272875848513862692501727630214597144877393921917775305030) * 10 ^ 70 +
        5652826316983765573641726104454260482430037230679419041903820912550965) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (419 - x)) = _
  rw [show 420 = 229 +
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
    rw [show 95 = 4 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (420 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (420 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_420 :
    recurrence4Scalar1Left.coeff 420 =
      -((((212802550572357516279276818998013942756872855859 * 10 ^ 70 +
        2952079727664940331509087990466261543387028886709537547051776657454939) * 10 ^ 70 +
        7045375904498403636574439865267542370522177742875207402955377624719073) * 10 ^ 70 +
        9928081166094371690554193953696438344467475339256811978058098127408297) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (420 - x)) = _
  rw [show 421 = 230 +
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
    rw [show 95 = 3 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (421 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (421 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_421 :
    recurrence4Scalar1Left.coeff 421 =
      ((((85485934851589261048121537841986589127367836226 * 10 ^ 70 +
        9226554947561281556844601239616532849331873963361472618191330679456930) * 10 ^ 70 +
        9218100292762478650690207657198514401693982352964041576581675256912819) * 10 ^ 70 +
        4784102538173421702272514605778261489462036194080591908961079321485280) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (421 - x)) = _
  rw [show 422 = 231 +
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
    rw [show 95 = 2 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (422 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (422 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_422 :
    recurrence4Scalar1Left.coeff 422 =
      -((((32162316501865814673465326214540829125997317131 * 10 ^ 70 +
        8634042671021146138533878564363120211999272491803526574007819747702961) * 10 ^ 70 +
        6116747266385140278723110149793709669615724471868184662133539799398663) * 10 ^ 70 +
        8683727173807980215388693580805732923079166274552759539602834003331337) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (422 - x)) = _
  rw [show 423 = 232 +
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
    rw [show 95 = 1 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (423 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (423 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_423 :
    recurrence4Scalar1Left.coeff 423 =
      ((((11481874743921516202302170479634166852776845910 * 10 ^ 70 +
        1178699175480294085065914435084039575835135000503029053277294987321254) * 10 ^ 70 +
        4189933263732237677157265446844914178947605976095126330153570848718749) * 10 ^ 70 +
        8783967675683629535835042393585389818222873933709738153407498383749465) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (423 - x)) = _
  rw [show 424 = 233 +
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
  rw [recurrence4Scalar1Left_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (424 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (424 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_424 :
    recurrence4Scalar1Left.coeff 424 =
      -((((3914663403823228204292044633680909866561209145 * 10 ^ 70 +
        2553596080157661507293674855882181731270374611353986082432277846207611) * 10 ^ 70 +
        0570989106528106227676889898097985479741373582980236723717353619064150) * 10 ^ 70 +
        3307234237222509036469599899541951082468260058078817185812007994787358) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (424 - x)) = _
  rw [show 425 = 234 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 31 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient1.coeff (425 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (425 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_425 :
    recurrence4Scalar1Left.coeff 425 =
      ((((1278372127621498003456893497531497334324378763 * 10 ^ 70 +
        7254472650410482461200304417954883076615316805277582380453341455389521) * 10 ^ 70 +
        7408983869057327636061937179926488988616130997670717205879135223382317) * 10 ^ 70 +
        3587970728232440711378235027570001689297850861633746163600141222564702) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (425 - x)) = _
  rw [show 426 = 235 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 30 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
