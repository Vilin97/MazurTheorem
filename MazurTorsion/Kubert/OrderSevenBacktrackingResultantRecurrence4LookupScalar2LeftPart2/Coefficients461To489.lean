/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart2Simp
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
  recurrence4A2_coeff_150
  recurrence4A2_coeff_151
  recurrence4A2_coeff_152
  recurrence4A2_coeff_153
  recurrence4A2_coeff_154
  recurrence4A2_coeff_155
  recurrence4A2_coeff_156
  recurrence4A2_coeff_157
  recurrence4A2_coeff_158
  recurrence4A2_coeff_159
  recurrence4A2_coeff_160
  recurrence4A2_coeff_161
  recurrence4A2_coeff_162
  recurrence4A2_coeff_163

attribute [local simp]
  recurrence4A2_coeff_164
  recurrence4A2_coeff_165
  recurrence4A2_coeff_166
  recurrence4A2_coeff_167
  recurrence4A2_coeff_168
  recurrence4A2_coeff_169
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
  recurrence4A2_coeff_180
  recurrence4A2_coeff_181
  recurrence4A2_coeff_182
  recurrence4A2_coeff_183
  recurrence4A2_coeff_184
  recurrence4A2_coeff_185
  recurrence4A2_coeff_186
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
  recurrence4A2_coeff_40
  recurrence4A2_coeff_41
  recurrence4A2_coeff_42
  recurrence4A2_coeff_43
  recurrence4A2_coeff_44
  recurrence4A2_coeff_45
  recurrence4A2_coeff_46
  recurrence4A2_coeff_47
  recurrence4A2_coeff_48
  recurrence4A2_coeff_49
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
  recurrence4A2_coeff_70

attribute [local simp]
  recurrence4A2_coeff_71
  recurrence4A2_coeff_72
  recurrence4A2_coeff_73
  recurrence4A2_coeff_74
  recurrence4A2_coeff_75
  recurrence4A2_coeff_76
  recurrence4A2_coeff_77
  recurrence4A2_coeff_78
  recurrence4A2_coeff_79
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar2Left_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 275,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (461 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (461 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_461 :
    recurrence4Scalar2Left.coeff 461 =
      ((((5195607978155525 * 10 ^ 70 +
        1115686689755348376488765462736583726060817322447838325517073931072244) * 10 ^ 70 +
        9706682681766049225422222989774677397076587876528587056052527436775876) * 10 ^ 70 +
        3005657153257176903289678679673683456621311789168205347462013499676219) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (461 - x)) = _
  rw [show 462 = 275 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 22 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 276,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (462 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (462 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_462 :
    recurrence4Scalar2Left.coeff 462 =
      -((((220008892151241 * 10 ^ 70 +
        3682252781606533405608460848958090980692664227037300306461036746637019) * 10 ^ 70 +
        1598749936477585752158543302787586566814493309008958970559397467669939) * 10 ^ 70 +
        3073424134178405428614393375409822593660882910821668830120179835141901) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (462 - x)) = _
  rw [show 463 = 276 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 21 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 277,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (463 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (463 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_463 :
    recurrence4Scalar2Left.coeff 463 =
      -((((2093933168459 * 10 ^ 70 +
        0463548787277066927091121703227192536546525204912623648253547345314005) * 10 ^ 70 +
        9263493028689754277452226204033781602850804546618780263520770344207633) * 10 ^ 70 +
        2622440234664817116967594798680265385202527650803530557590222442506276) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (463 - x)) = _
  rw [show 464 = 277 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 20 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_463_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 278,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (464 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (464 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_464 :
    recurrence4Scalar2Left.coeff 464 =
      ((((1448358195719 * 10 ^ 70 +
        6265161717375611422444443048465833713884451788913641411820446337987227) * 10 ^ 70 +
        5111192096065166187684265999815913763956174964309671741441938547679122) * 10 ^ 70 +
        8863077471433670316338827256469748386932601201831298860372492890417549) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (464 - x)) = _
  rw [show 465 = 278 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 19 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_464_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 279,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (465 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (465 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_465 :
    recurrence4Scalar2Left.coeff 465 =
      -((((157748363291 * 10 ^ 70 +
        8668388000560056056755387707024857196724165942921887216587342957858312) * 10 ^ 70 +
        9734360932773449006269935023379684538649744349634474100324752416711835) * 10 ^ 70 +
        3738963567129152054585146642105398112936775190003009662499399400941186) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (465 - x)) = _
  rw [show 466 = 279 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 18 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_465_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 280,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (466 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (466 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_466 :
    recurrence4Scalar2Left.coeff 466 =
      ((((10853732806 * 10 ^ 70 +
        7407686281001423564229402725439533494956840695246416475813449768978414) * 10 ^ 70 +
        2759949388684503722234699338429039953156920131777605572251016225266201) * 10 ^ 70 +
        5748793474163765269535013085670153369641063058454116062251021693014826) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (466 - x)) = _
  rw [show 467 = 280 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 17 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_466_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 281,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (467 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (467 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_467 :
    recurrence4Scalar2Left.coeff 467 =
      -((((500626312 * 10 ^ 70 +
        3267248047145218034908499201438536676302291317719267479358664151170783) * 10 ^ 70 +
        9148551876918932187243550323040570736016177582336149248895471910776479) * 10 ^ 70 +
        5444431168886479986934375699145942652763374659115014695726818561170924) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (467 - x)) = _
  rw [show 468 = 281 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 16 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_467_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 282,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (468 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (468 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_468 :
    recurrence4Scalar2Left.coeff 468 =
      ((((11867582 * 10 ^ 70 +
        9117661176534081674763275798157958790168108314436521009730407823907604) * 10 ^ 70 +
        2019776349614608166121663713723710167367771481084011369530201945081523) * 10 ^ 70 +
        5842316290367601097185086375599408190085531872651300528852578982666058) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (468 - x)) = _
  rw [show 469 = 282 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 15 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_468_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_469_prefix_zero :
    (∑ x ∈ Finset.range 283,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (469 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (469 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_469_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (469 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_469 :
    recurrence4Scalar2Left.coeff 469 =
      ((((287611 * 10 ^ 70 +
        8986643804276758840844885382323679502345448547216666376451423113612481) * 10 ^ 70 +
        2386208315364040796971280344711788089417188813849556108691543656031095) * 10 ^ 70 +
        3313716920897508994742701709412919614319677588887024923914018015128856) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 470,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (469 - x)) = _
  rw [show 470 = 283 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 14 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_469_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_469_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_470_prefix_zero :
    (∑ x ∈ Finset.range 284,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (470 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (470 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_470_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (470 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_470 :
    recurrence4Scalar2Left.coeff 470 =
      -((((42271 * 10 ^ 70 +
        2318096464655900051741985977104130975130557484011306981148346996705264) * 10 ^ 70 +
        1884418204947317711112442684094437871398835661332951655529749140737918) * 10 ^ 70 +
        1573176683270643636443725197223804722475125539134060704630528461889627) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 471,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (470 - x)) = _
  rw [show 471 = 284 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 13 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_470_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_470_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_471_prefix_zero :
    (∑ x ∈ Finset.range 285,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (471 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (471 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_471_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (471 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_471 :
    recurrence4Scalar2Left.coeff 471 =
      ((((1965 * 10 ^ 70 +
        0942842719379591015446233432835756162722398437529475348097077644526388) * 10 ^ 70 +
        3697990625985723752040611813670937034607239540694773522777537529159655) * 10 ^ 70 +
        4032810863231593449906780291735808413516298966780435581537944905559139) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 472,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (471 - x)) = _
  rw [show 472 = 285 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 12 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_471_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_471_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_472_prefix_zero :
    (∑ x ∈ Finset.range 286,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (472 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (472 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_472_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (472 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_472 :
    recurrence4Scalar2Left.coeff 472 =
      -((((41 * 10 ^ 70 +
        4063950631997650183619748014208974689836162760819708306993773204079504) * 10 ^ 70 +
        4424940604634429333393880390841422196461907900382266437156600375674293) * 10 ^ 70 +
        2625460216692103642070203372850676902189568193682627144542931608177552) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 473,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (472 - x)) = _
  rw [show 473 = 286 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 11 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_472_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_472_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_473_prefix_zero :
    (∑ x ∈ Finset.range 287,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (473 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (473 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_473_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (473 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_473 :
    recurrence4Scalar2Left.coeff 473 =
      -(((3257370312778615221637997911683363945732684975818138050994339139669967 * 10 ^ 70 +
        5718978700098846206273920479426890123762828282822440878102089351759746) * 10 ^ 70 +
        3058732578885438914066017280840909473710652696306259020865145761623549) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 474,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (473 - x)) = _
  rw [show 474 = 287 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 10 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_473_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_473_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_474_prefix_zero :
    (∑ x ∈ Finset.range 288,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (474 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (474 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_474_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (474 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_474 :
    recurrence4Scalar2Left.coeff 474 =
      (((431893996961065423838969530126388799143570221474810941615871833340405 * 10 ^ 70 +
        1175244326083672993911367896102873074123859464384144751136565502873944) * 10 ^ 70 +
        7403644277616772445160791468659945310180830732110067076826524102246178) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 475,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (474 - x)) = _
  rw [show 475 = 288 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 9 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_474_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_474_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_475_prefix_zero :
    (∑ x ∈ Finset.range 289,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (475 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (475 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_475_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (475 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_475 :
    recurrence4Scalar2Left.coeff 475 =
      -(((8699007739552546716773914844575482911973880650356219984911599949583 * 10 ^ 70 +
        9717589189579512712727907215664553824326780495407513115372202251490368) * 10 ^ 70 +
        1750954718780492753594285365479824266506275819703600883447971668424658) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 476,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (475 - x)) = _
  rw [show 476 = 289 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 8 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_475_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_475_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_476_prefix_zero :
    (∑ x ∈ Finset.range 290,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (476 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (476 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_476_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (476 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_476 :
    recurrence4Scalar2Left.coeff 476 =
      -(((43090521349718311476840999464135472531102986075675437387778590315 * 10 ^ 70 +
        4139630417587685544526017393639477469425998806068286960598707430847046) * 10 ^ 70 +
        5643206625841609829236166929827905713366344679722430135258674711843075) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 477,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (476 - x)) = _
  rw [show 477 = 290 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 7 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_476_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_476_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_477_prefix_zero :
    (∑ x ∈ Finset.range 291,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (477 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (477 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_477_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (477 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_477 :
    recurrence4Scalar2Left.coeff 477 =
      (((3478309230957860055769347664465270141071000530602651891560797338 * 10 ^ 70 +
        4096932541269642489146414493641107081076941431290888525954521302979223) * 10 ^ 70 +
        4653337311040322110592667262136755159767994408044882497091176754514823) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 478,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (477 - x)) = _
  rw [show 478 = 291 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 6 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_477_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_477_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_478_prefix_zero :
    (∑ x ∈ Finset.range 292,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (478 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (478 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_478_suffix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (478 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_478 :
    recurrence4Scalar2Left.coeff 478 =
      -(((11964092151908318507467355459023430140265648979050666500985359 * 10 ^ 70 +
        1157203503759777372697495905262293950095049118074638842627411469396652) * 10 ^ 70 +
        9571631071560808495564513915125704021090022573444653669078288444807122) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 479,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (478 - x)) = _
  rw [show 479 = 292 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 5 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_478_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_478_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_479_prefix_zero :
    (∑ x ∈ Finset.range 293,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (479 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (479 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_479_suffix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (479 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_479 :
    recurrence4Scalar2Left.coeff 479 =
      -(((591154847903726400970581097772845468356311306891257492979599 * 10 ^ 70 +
        7121416335022721217315660687714754026843513381858239447984243282780603) * 10 ^ 70 +
        0333545887363300287081538622297944187451933802179137991776440947206106) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 480,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (479 - x)) = _
  rw [show 480 = 293 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 4 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_479_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_479_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_480_prefix_zero :
    (∑ x ∈ Finset.range 294,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (480 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (480 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_480_suffix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (480 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_480 :
    recurrence4Scalar2Left.coeff 480 =
      (((1781095777866350687961040615594806070683105911959588402274 * 10 ^ 70 +
        8741995260596668973887530424074950142510999010441415242594531746446597) * 10 ^ 70 +
        0184723804486900687290946172567554599130687082263360529941496347872189) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 481,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (480 - x)) = _
  rw [show 481 = 294 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 3 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_480_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_480_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_481_prefix_zero :
    (∑ x ∈ Finset.range 295,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (481 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (481 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_481_suffix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (481 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_481 :
    recurrence4Scalar2Left.coeff 481 =
      (((56572847228842456422901581309817646297546672565303143020 * 10 ^ 70 +
        0550796713726972265643794801062954257279693657998352508757284173396778) * 10 ^ 70 +
        7947628094738616448801252836552719542279024294462160352143318194918554) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 482,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (481 - x)) = _
  rw [show 482 = 295 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 2 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_481_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_481_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_482_prefix_zero :
    (∑ x ∈ Finset.range 296,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (482 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (482 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_482_suffix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (482 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_482 :
    recurrence4Scalar2Left.coeff 482 =
      -(((6588901554284596095313409911562086382678291906772608 * 10 ^ 70 +
        0612876722517431218939320648748024687213198946863808635475294365139078) * 10 ^ 70 +
        4854904984526101383585291631810185385557849169831095635250159732878517) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 483,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (482 - x)) = _
  rw [show 483 = 296 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 1 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_482_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_482_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_483_prefix_zero :
    (∑ x ∈ Finset.range 297,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (483 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (483 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_483_suffix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (483 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_483 :
    recurrence4Scalar2Left.coeff 483 =
      -(((2520182549979306304800161997611555400712833889054990 * 10 ^ 70 +
        2216869425917039980051856065829162313612661487281851639059642346258029) * 10 ^ 70 +
        9900417695066921270629748296671857661988554547080060114841941618907128) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 484,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (483 - x)) = _
  rw [show 484 = 297 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_483_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_483_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_484_prefix_zero :
    (∑ x ∈ Finset.range 298,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (484 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (484 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_484_suffix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (484 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_484 :
    recurrence4Scalar2Left.coeff 484 =
      -(((3912281446394025715272358044769956793288684803911 * 10 ^ 70 +
        7727045559420187113063068116668930825226361308877282836232074329842583) * 10 ^ 70 +
        3607160358500002621202673682330178657165709118459880545808939903318356) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 485,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (484 - x)) = _
  rw [show 485 = 298 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 31 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_484_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_484_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_485_prefix_zero :
    (∑ x ∈ Finset.range 299,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (485 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (485 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_485_suffix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (485 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_485 :
    recurrence4Scalar2Left.coeff 485 =
      (((54487697609868225671193490158449120376303932174 * 10 ^ 70 +
        0868668314413640865242061637170767552454091990806606569638200581533683) * 10 ^ 70 +
        5898712846485633074574990837474846923762809734543318547680597342567054) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 486,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (485 - x)) = _
  rw [show 486 = 299 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 30 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_485_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_485_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_486_prefix_zero :
    (∑ x ∈ Finset.range 300,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (486 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (486 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_486_suffix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (486 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_486 :
    recurrence4Scalar2Left.coeff 486 =
      (((130423936972181799823155727158036309805411957 * 10 ^ 70 +
        3522164028348769194978832941963273108868265985605399590722072845832753) * 10 ^ 70 +
        4086855687195610557863247886776221913553032651573747656186860585921841) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 487,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (486 - x)) = _
  rw [show 487 = 300 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 29 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_486_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_486_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_487_prefix_zero :
    (∑ x ∈ Finset.range 301,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (487 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (487 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_487_suffix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (487 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_487 :
    recurrence4Scalar2Left.coeff 487 =
      -(((613921033389389689195702609686329740987955 * 10 ^ 70 +
        5787013660001316049795138328307803938527586851767728088245080528734508) * 10 ^ 70 +
        3497634860184175763000353512830903977507147696859078026761761944961626) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 488,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (487 - x)) = _
  rw [show 488 = 301 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 28 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_487_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_487_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_488_prefix_zero :
    (∑ x ∈ Finset.range 302,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (488 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (488 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_488_suffix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (488 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_488 :
    recurrence4Scalar2Left.coeff 488 =
      -(((1636155860588797259421959362477917188912 * 10 ^ 70 +
        5634790556342186593503950344113590472487818580661768952956045624354495) * 10 ^ 70 +
        0696047250892501296519936402924211456138138612471888279849842649986596) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 489,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (488 - x)) = _
  rw [show 489 = 302 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 27 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_488_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_488_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_489_prefix_zero :
    (∑ x ∈ Finset.range 303,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (489 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (489 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_489_suffix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (489 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_489 :
    recurrence4Scalar2Left.coeff 489 =
      (((4303643889618364186628810103902607322 * 10 ^ 70 +
        6188227881682108922270161984457506827058224204553290401464284443521589) * 10 ^ 70 +
        2362096371610240721251475565445769736853305068055657376371915217310365) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 490,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (489 - x)) = _
  rw [show 490 = 303 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 26 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_489_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_489_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
