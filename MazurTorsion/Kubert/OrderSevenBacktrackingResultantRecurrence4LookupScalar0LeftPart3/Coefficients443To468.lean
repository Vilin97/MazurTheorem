/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart3Simp
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
  recurrence4A0_coeff_150
  recurrence4A0_coeff_151
  recurrence4A0_coeff_152
  recurrence4A0_coeff_153
  recurrence4A0_coeff_154
  recurrence4A0_coeff_155
  recurrence4A0_coeff_156
  recurrence4A0_coeff_157
  recurrence4A0_coeff_158
  recurrence4A0_coeff_159
  recurrence4A0_coeff_160
  recurrence4A0_coeff_161
  recurrence4A0_coeff_162
  recurrence4A0_coeff_163

attribute [local simp]
  recurrence4A0_coeff_164
  recurrence4A0_coeff_165
  recurrence4A0_coeff_166
  recurrence4A0_coeff_167
  recurrence4A0_coeff_168
  recurrence4A0_coeff_169
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
  recurrence4A0_coeff_190
  recurrence4A0_coeff_191
  recurrence4A0_coeff_192
  recurrence4A0_coeff_193
  recurrence4A0_coeff_194
  recurrence4A0_coeff_43
  recurrence4A0_coeff_44
  recurrence4A0_coeff_45
  recurrence4A0_coeff_46
  recurrence4A0_coeff_47
  recurrence4A0_coeff_48
  recurrence4A0_coeff_49
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
  recurrence4A0_coeff_70
  recurrence4A0_coeff_71
  recurrence4A0_coeff_72
  recurrence4A0_coeff_73
  recurrence4A0_coeff_74
  recurrence4A0_coeff_75

attribute [local simp]
  recurrence4A0_coeff_76
  recurrence4A0_coeff_77
  recurrence4A0_coeff_78
  recurrence4A0_coeff_79
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
  recurrence4A0_coeff_90
  recurrence4A0_coeff_91
  recurrence4A0_coeff_92
  recurrence4A0_coeff_93
  recurrence4A0_coeff_94
  recurrence4A0_coeff_95
  recurrence4A0_coeff_96
  recurrence4A0_coeff_97
  recurrence4A0_coeff_98
  recurrence4A0_coeff_99
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

attribute [local simp]
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

attribute [local simp]
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

private theorem recurrence4Scalar0Left_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (443 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (443 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_443 :
    recurrence4Scalar0Left.coeff 443 =
      ((((8175485595351389694874733374377939603 * 10 ^ 70 +
        6655197559696977950096413437446585987904132322079170939788789367978580) * 10 ^ 70 +
        0019053916074660933867037307124657262314654180604206972001607241827748) * 10 ^ 70 +
        2362053105961387706643138144503656267426587807493078443730833248751367) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (443 - x)) = _
  rw [show 444 = 249 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 16 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_443_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (444 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (444 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_444 :
    recurrence4Scalar0Left.coeff 444 =
      -((((1904793902169644595570288735877075546 * 10 ^ 70 +
        4900869844521818768102976675333958157079071907170851793012268749948844) * 10 ^ 70 +
        3442840974520558899157099110940289973115611509240489984423283749500759) * 10 ^ 70 +
        7341840536490671441736867045098553104237578050134155732965802025208371) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (444 - x)) = _
  rw [show 445 = 250 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 15 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_444_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (445 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (445 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_445 :
    recurrence4Scalar0Left.coeff 445 =
      ((((416556063903147987151234429851172649 * 10 ^ 70 +
        1495193822699178278896311690755504785541285964666904678485621792429302) * 10 ^ 70 +
        6591868708792713732480168937044612809155298563786479655868338919782318) * 10 ^ 70 +
        9450261728712239858941647146561541736445605796660667405115836496265572) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (445 - x)) = _
  rw [show 446 = 251 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 14 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_445_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (446 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (446 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_446 :
    recurrence4Scalar0Left.coeff 446 =
      -((((85770059912940887411556499819073869 * 10 ^ 70 +
        2582084055122324817694558594140681785072767115492297685578307664865888) * 10 ^ 70 +
        6578678949320978005784464592353293092771462278220169283252526048156762) * 10 ^ 70 +
        4556056356391956423598843289311631882098371433323111986802961488317336) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (446 - x)) = _
  rw [show 447 = 252 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 13 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_446_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (447 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (447 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_447 :
    recurrence4Scalar0Left.coeff 447 =
      ((((16648025075494869171940332227516223 * 10 ^ 70 +
        6503465627493865584717034819559241705567551494240521239047488079712221) * 10 ^ 70 +
        5692046248175760124678447978140172275284025595424549512780579485056473) * 10 ^ 70 +
        3277629595673485643017977405072348784077512304225703686059421740839291) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (447 - x)) = _
  rw [show 448 = 253 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 12 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_447_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (448 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (448 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_448 :
    recurrence4Scalar0Left.coeff 448 =
      -((((3045582895736350585279278899829466 * 10 ^ 70 +
        7116344714537777919589291617354223056147996631657500694992099810590660) * 10 ^ 70 +
        8383049354355337534259590143888037898844219953057460633203014239022385) * 10 ^ 70 +
        0580558469432321565745659328868596044981152242344146094033637212984753) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (448 - x)) = _
  rw [show 449 = 254 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 11 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_448_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (449 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (449 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_449 :
    recurrence4Scalar0Left.coeff 449 =
      ((((524350332042033715240138186965935 * 10 ^ 70 +
        1507412642074593855344252230954158165314995301913471049850518009905491) * 10 ^ 70 +
        5419254321744243209865621282877842647852115848586158575541619711556797) * 10 ^ 70 +
        2972654181773116089926273920611180456026640019384253020469443855269405) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (449 - x)) = _
  rw [show 450 = 255 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 10 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_449_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (450 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (450 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_450 :
    recurrence4Scalar0Left.coeff 450 =
      -((((84716051899899078355920862856604 * 10 ^ 70 +
        3870534527823081728525278754374515998016361875754830329241854926272523) * 10 ^ 70 +
        9547775530648755420932421994425314943445719461863073737630604869613117) * 10 ^ 70 +
        7866706418656817177180222208644504326492614011112303234559356059010978) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (450 - x)) = _
  rw [show 451 = 256 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 9 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_450_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (451 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (451 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_451 :
    recurrence4Scalar0Left.coeff 451 =
      ((((12782937630894926282436665844912 * 10 ^ 70 +
        8212216651390470719983219443743717883969744920270024070428254752594350) * 10 ^ 70 +
        7853403965108302319721586626741842808517288511829381620840536116866948) * 10 ^ 70 +
        4446013241558496927774548413862502534843743042116946613684410850892754) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (451 - x)) = _
  rw [show 452 = 257 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 8 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_451_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (452 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (452 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_452 :
    recurrence4Scalar0Left.coeff 452 =
      -((((1787511679305239192396086324746 * 10 ^ 70 +
        9503169678683829773712494594583259898657963247199625989190395310895366) * 10 ^ 70 +
        2538122340295388603876859438644149871285437442271927213153554672837336) * 10 ^ 70 +
        0408729720724549033525944673855850141349273240123636630093838040311539) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (452 - x)) = _
  rw [show 453 = 258 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 7 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_452_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (453 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (453 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_453 :
    recurrence4Scalar0Left.coeff 453 =
      ((((228608306320460439445322049419 * 10 ^ 70 +
        4134030438812731821493234296189397455293943190536904921450771337049612) * 10 ^ 70 +
        9545202633484631479015740960928754406024662833257769172952259581550905) * 10 ^ 70 +
        1470454159514173903400688825487277184981078488550862341014915064473346) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (453 - x)) = _
  rw [show 454 = 259 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 6 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_453_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (454 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (454 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_454 :
    recurrence4Scalar0Left.coeff 454 =
      -((((26084906234801769128977546681 * 10 ^ 70 +
        5015248651718674686115523513786363408444539149534803597623995546133340) * 10 ^ 70 +
        1516810937627746887947024717870963916163659545857530068819548261618577) * 10 ^ 70 +
        1730689643822176479490934135153594540582418276430030230923777511723054) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (454 - x)) = _
  rw [show 455 = 260 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 5 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_454_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (455 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (455 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_455 :
    recurrence4Scalar0Left.coeff 455 =
      ((((2511485952967347485689124323 * 10 ^ 70 +
        2915475471897644145433189264435304088792642904326247278096697584303948) * 10 ^ 70 +
        3633536729196819501841719513275838265755773098592504759440542422207007) * 10 ^ 70 +
        2808149979777417776322038709600351709504271045935729581219242169151230) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (455 - x)) = _
  rw [show 456 = 261 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 4 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_455_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (456 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (456 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_456 :
    recurrence4Scalar0Left.coeff 456 =
      -((((170464934450206920348406707 * 10 ^ 70 +
        7182656182624485576701635499684613291452895358505115970691292929682322) * 10 ^ 70 +
        1615492117319290384902917074376977799374539156172769834239673623796574) * 10 ^ 70 +
        1247790402525546773194055883324481986277932124291006108827219451400119) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (456 - x)) = _
  rw [show 457 = 262 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 3 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_456_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (457 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (457 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_457 :
    recurrence4Scalar0Left.coeff 457 =
      -((((782114445600558407177154 * 10 ^ 70 +
        1216214251007969046618956654101996918283470001364406806566431540889165) * 10 ^ 70 +
        8307193660941261583598799090313255613576943327461652656499257557829999) * 10 ^ 70 +
        2608177534062421026559361893581931213245436611351471731272894221923102) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (457 - x)) = _
  rw [show 458 = 263 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 2 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_457_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (458 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (458 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_458 :
    recurrence4Scalar0Left.coeff 458 =
      ((((2970279138219661135340255 * 10 ^ 70 +
        0716965339136940373259055218330413501442906526588751652496768409464924) * 10 ^ 70 +
        2071082871361623755795426543349388733501700629447061802021116227282202) * 10 ^ 70 +
        2492011295360247198244468497645494811898789996964007491315184442385423) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (458 - x)) = _
  rw [show 459 = 264 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 1 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_458_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (459 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (459 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_459 :
    recurrence4Scalar0Left.coeff 459 =
      -((((684851764694885623899637 * 10 ^ 70 +
        1218237246183099412376541113057154161706155955474986608445344314067500) * 10 ^ 70 +
        2718268206116305502861460728698436074236249419675785515806119580092101) * 10 ^ 70 +
        9134616314954495559498103433190246995769459225598299695467546254683451) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (459 - x)) = _
  rw [show 460 = 265 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_459_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (460 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (460 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_460 :
    recurrence4Scalar0Left.coeff 460 =
      ((((112402740306963453148726 * 10 ^ 70 +
        4894037245283400001584233206881750591980950475878848638890749304517266) * 10 ^ 70 +
        1101780874390521194140937559724540387961103691856500253659096347293452) * 10 ^ 70 +
        5097427225928690900907275143521376343314590712983612804020153306434423) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (460 - x)) = _
  rw [show 461 = 266 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 31 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_460_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_461_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (461 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (461 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_461_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (461 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (461 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_461 :
    recurrence4Scalar0Left.coeff 461 =
      -((((15318203046925605826229 * 10 ^ 70 +
        2071451446323328098130464449007485237157705806238273704751197967186373) * 10 ^ 70 +
        5248040225813472109151470593265256132202099080315391307121446919346082) * 10 ^ 70 +
        8949246970781898210350254983334870804036564072979180245109247681999334) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 462,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (461 - x)) = _
  rw [show 462 = 267 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 30 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_461_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_461_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_462_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (462 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (462 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_462_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (462 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (462 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_462 :
    recurrence4Scalar0Left.coeff 462 =
      ((((1803681361867217709899 * 10 ^ 70 +
        5816059134977549744419452294228448912080198480622480030244288728302615) * 10 ^ 70 +
        1462783354890307844372386671462082091435287128663188419379685188896814) * 10 ^ 70 +
        5228922483641195506179293322684916305443648763345887906987308918687500) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 463,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (462 - x)) = _
  rw [show 463 = 268 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 29 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_462_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_462_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_463_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (463 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (463 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_463_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (463 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (463 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_463 :
    recurrence4Scalar0Left.coeff 463 =
      -((((184258016620918380677 * 10 ^ 70 +
        6604093111839596713926178924828192048819672542555190931652271063368551) * 10 ^ 70 +
        9680573690237640772648976744115479984697370542692544330420491301197934) * 10 ^ 70 +
        2701751113714751925134453470928593070352930386082859705855587724827729) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 464,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (463 - x)) = _
  rw [show 464 = 269 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 28 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_463_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_463_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_464_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (464 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (464 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_464_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (464 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (464 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_464 :
    recurrence4Scalar0Left.coeff 464 =
      ((((15979696441038758100 * 10 ^ 70 +
        6483475009637965557393470815657225119145536792369200796217758336819135) * 10 ^ 70 +
        0669096809502561287903462334367383833414360660758901241303069326615968) * 10 ^ 70 +
        1249194228780004682963678822999076437232157218783201412755710238016820) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 465,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (464 - x)) = _
  rw [show 465 = 270 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 27 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_464_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_464_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_465_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (465 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (465 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_465_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (465 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (465 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_465 :
    recurrence4Scalar0Left.coeff 465 =
      -((((1099163150635655059 * 10 ^ 70 +
        2378702912640585950743723419721687628739457910896826658062125387323268) * 10 ^ 70 +
        9249501752043327884839531011799689964533207931774674683978120931201762) * 10 ^ 70 +
        8664338522702751198486455893198158759923695035123857395914183346056632) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 466,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (465 - x)) = _
  rw [show 466 = 271 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 26 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_465_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_465_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_466_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (466 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (466 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_466_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (466 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (466 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_466 :
    recurrence4Scalar0Left.coeff 466 =
      ((((46290034165941428 * 10 ^ 70 +
        3830186665175652216482792792417612956637768137047167089300650742926033) * 10 ^ 70 +
        9670562077851233389488755315038831541405220574525449613677550000819646) * 10 ^ 70 +
        0707801801289700397396969828317967946258080634208796626460246207387891) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 467,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (466 - x)) = _
  rw [show 467 = 272 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 25 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_466_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_466_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_467_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (467 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (467 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_467_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (467 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (467 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_467 :
    recurrence4Scalar0Left.coeff 467 =
      ((((1387891292102210 * 10 ^ 70 +
        2643682394175772217257863549412774107813454761640199225797480418914996) * 10 ^ 70 +
        4635316163905031022400293964556691480115258489351578759642150986347230) * 10 ^ 70 +
        5299448681315104806516052218071823546881489854639061554797882531068135) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 468,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (467 - x)) = _
  rw [show 468 = 273 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 24 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_467_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_467_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Left_coeff_468_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (468 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (468 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_468_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient0.coeff (468 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 329 + x
  · rw [recurrence4LeadingSquare_coeff_high (329 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (468 - (329 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_468 :
    recurrence4Scalar0Left.coeff 468 =
      -((((544488088855786 * 10 ^ 70 +
        6213351020176951984887244390420798339144671827656386491539008660833716) * 10 ^ 70 +
        6174862959922420926567931813657832554761243678933928557847859078725361) * 10 ^ 70 +
        1619972544858727865584102646478257317757248836579793654759726610065241) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 469,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (468 - x)) = _
  rw [show 469 = 274 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 23 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_468_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_468_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
