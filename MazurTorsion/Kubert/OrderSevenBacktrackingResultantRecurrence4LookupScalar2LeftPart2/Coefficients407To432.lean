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

private theorem recurrence4Scalar2Left_coeff_407_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (407 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (407 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_407_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (407 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_407 :
    recurrence4Scalar2Left.coeff 407 =
      ((((14037283840209126379681056550909742665168084417250220 * 10 ^ 70 +
        5608217981408558865977163373440493778233779523108563746415463751991963) * 10 ^ 70 +
        9799117056152075994144654203392724259456838525226180713917222684913567) * 10 ^ 70 +
        7697583325411548539134384988381042670045538925744418781098057161282325) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 408,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (407 - x)) = _
  rw [show 408 = 221 +
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
    rw [show 91 = 12 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_407_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_407_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_408_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (408 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (408 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_408_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (408 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_408 :
    recurrence4Scalar2Left.coeff 408 =
      -((((4200013804146119815535734396203300291571856594590057 * 10 ^ 70 +
        2466913724194785139044700034955068418464714765719761132837786098635170) * 10 ^ 70 +
        3731541627245144740654362412565582533471167992590372257729386333365027) * 10 ^ 70 +
        3023857823091276471335943895590892293963957596740170615223823370002370) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 409,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (408 - x)) = _
  rw [show 409 = 222 +
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
    rw [show 91 = 11 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_408_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_408_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_409_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (409 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (409 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_409_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (409 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_409 :
    recurrence4Scalar2Left.coeff 409 =
      ((((1098943874436355151095648008100950769813587497064272 * 10 ^ 70 +
        9282607601820148439028404123587544843639495483483735072470930927340115) * 10 ^ 70 +
        8445881140775728731425584195836057534339258531645458210474209848030439) * 10 ^ 70 +
        1038739562872003223761975786113405773608146738322020799938863747233273) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 410,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (409 - x)) = _
  rw [show 410 = 223 +
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
    rw [show 91 = 10 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_409_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_409_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_410_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (410 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (410 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_410_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (410 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_410 :
    recurrence4Scalar2Left.coeff 410 =
      -((((227527466076644583846103849195596516317292882189310 * 10 ^ 70 +
        0702978504190175329292860474537346122034644598138342235808609736494863) * 10 ^ 70 +
        4782892295164099146790256807519826341994633573972614955738625344958311) * 10 ^ 70 +
        7654176017204929275853119436753527369180416276342097580489377496001343) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 411,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (410 - x)) = _
  rw [show 411 = 224 +
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
    rw [show 91 = 9 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_410_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_410_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_411_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (411 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (411 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_411_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (411 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_411 :
    recurrence4Scalar2Left.coeff 411 =
      ((((20291763255669410545474780762982652055968615310913 * 10 ^ 70 +
        3970991148012799969484978918395250394905776509415564163495071633587391) * 10 ^ 70 +
        3349197163847621530668110803769691846205262174484575357675464074980037) * 10 ^ 70 +
        3701016814028457059819604482283175428971450338182849038837324450006062) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 412,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (411 - x)) = _
  rw [show 412 = 225 +
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
    rw [show 91 = 8 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_411_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_411_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_412_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (412 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (412 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_412_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (412 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_412 :
    recurrence4Scalar2Left.coeff 412 =
      ((((13587829239689476127059194707229014941684873792171 * 10 ^ 70 +
        6195022057536186695677537015878556038572929231963712651777160122762973) * 10 ^ 70 +
        5943124803411574459130379877665111935943538490447417697548778879544084) * 10 ^ 70 +
        4955678661160101267235845700024806193141917795497406966522514963339919) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 413,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (412 - x)) = _
  rw [show 413 = 226 +
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
    rw [show 91 = 7 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_412_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_412_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_413_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (413 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (413 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_413_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (413 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_413 :
    recurrence4Scalar2Left.coeff 413 =
      -((((11508344951535161649145027441851644557163307350156 * 10 ^ 70 +
        6773738278797132408856655031569323494836447036220414926769354545998417) * 10 ^ 70 +
        2737433671156261527159859814039763782285329290853994746093461981404673) * 10 ^ 70 +
        5017661172915347860069258999705251171855536430374241966606140212514583) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 414,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (413 - x)) = _
  rw [show 414 = 227 +
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
    rw [show 91 = 6 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_413_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_413_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_414_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (414 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (414 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_414_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (414 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_414 :
    recurrence4Scalar2Left.coeff 414 =
      ((((6097566519129577841793799885644045737017658040135 * 10 ^ 70 +
        0677492593665709180798710528119105816125591935989050151613026420429383) * 10 ^ 70 +
        5256816933429674281369796849826903412633474545908699291535131054629514) * 10 ^ 70 +
        9952664838550767715673531204424893710275663757747186821293584075955320) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 415,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (414 - x)) = _
  rw [show 415 = 228 +
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
    rw [show 91 = 5 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_414_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_414_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_415_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (415 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (415 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_415_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (415 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_415 :
    recurrence4Scalar2Left.coeff 415 =
      -((((2725821033410804019275615850618369684810335244502 * 10 ^ 70 +
        9257394715502660514694143048168599458851009651581028964048344496754295) * 10 ^ 70 +
        2698756234140490910354956063267059037370668450361564900075675838696391) * 10 ^ 70 +
        1407587545027072245984251200007597602076660854253692299203577846608043) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 416,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (415 - x)) = _
  rw [show 416 = 229 +
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
    rw [show 91 = 4 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_415_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_415_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_416_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (416 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (416 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_416_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (416 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_416 :
    recurrence4Scalar2Left.coeff 416 =
      ((((1108329548594360737369687955626276998735493679186 * 10 ^ 70 +
        7820738664196224103756483164200628928062162876262326772310700946812723) * 10 ^ 70 +
        3215654261055290943985870575738777125727450402724035519453979657265334) * 10 ^ 70 +
        1233325232985889204290198155532571577610783259676619449563642701949983) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 417,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (416 - x)) = _
  rw [show 417 = 230 +
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
    rw [show 91 = 3 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_416_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_416_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_417_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (417 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (417 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_417_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (417 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_417 :
    recurrence4Scalar2Left.coeff 417 =
      -((((422481658699015212744347573911489686804897733987 * 10 ^ 70 +
        7770474316255422575115775185894699026923461889178305857394554962751508) * 10 ^ 70 +
        3305003803225560689189165202158654724719065069766068314379536253198641) * 10 ^ 70 +
        5643433008522821933147663766504631553354141764692606348729302489209989) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 418,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (417 - x)) = _
  rw [show 418 = 231 +
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
    rw [show 91 = 2 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_417_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_417_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_418_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (418 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (418 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_418_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (418 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_418 :
    recurrence4Scalar2Left.coeff 418 =
      ((((153218232223868071546027055412929689237354055010 * 10 ^ 70 +
        4966067065312458031242221382370473804604595707193209277011029185683613) * 10 ^ 70 +
        2172056099058997582367881700749135058214347659305918901696292412917896) * 10 ^ 70 +
        7505735917815384214357167907537257170956644079780012948997326761452356) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 419,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (418 - x)) = _
  rw [show 419 = 232 +
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
    rw [show 91 = 1 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_418_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_418_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_419_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (419 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (419 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_419_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (419 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_419 :
    recurrence4Scalar2Left.coeff 419 =
      -((((53277106830615301596702112763865384897195046488 * 10 ^ 70 +
        1134652059283122979670535446827773451198757783348075831528888934946278) * 10 ^ 70 +
        4900150041276340531842541611138055599858572937297535186804508966358437) * 10 ^ 70 +
        8031442846133622098986454353424613854971314688512671090711203974388484) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 420,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (419 - x)) = _
  rw [show 420 = 233 +
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
  rw [recurrence4Scalar2Left_coeff_419_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_419_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_420_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (420 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (420 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_420_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (420 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_420 :
    recurrence4Scalar2Left.coeff 420 =
      ((((17833851756745589041588007178425185934182649926 * 10 ^ 70 +
        9807659668457112728445590859635006107229086213863705937820706374460260) * 10 ^ 70 +
        4592198544570914857625758699389662571461382863745754349950549468181287) * 10 ^ 70 +
        1786956899001387004786663419548124581957730780020681699164333929707334) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 421,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (420 - x)) = _
  rw [show 421 = 234 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 31 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_420_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_420_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_421_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (421 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (421 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_421_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (421 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_421 :
    recurrence4Scalar2Left.coeff 421 =
      -((((5756840070799112528178896977526376454728726478 * 10 ^ 70 +
        7510713400627606119862085738845791174510279969761300903701103378056372) * 10 ^ 70 +
        7103494040100918679523874451753851323069260384584950461149931243472077) * 10 ^ 70 +
        9362059369123905906631501446399181123629611633213492488326499084276633) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 422,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (421 - x)) = _
  rw [show 422 = 235 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 30 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_421_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_421_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_422_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (422 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (422 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_422_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (422 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_422 :
    recurrence4Scalar2Left.coeff 422 =
      ((((1792384593817699792764246935340840027473931051 * 10 ^ 70 +
        6565286764864004971456572341919525511897697646540862233481867954144048) * 10 ^ 70 +
        1235097421955700891370258062082696095439113854040307659382616193736139) * 10 ^ 70 +
        9438786787780187337160983103962352756762996787479975617176889092251972) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 423,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (422 - x)) = _
  rw [show 423 = 236 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 29 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_422_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_422_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_423_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (423 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (423 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_423_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (423 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_423 :
    recurrence4Scalar2Left.coeff 423 =
      -((((537655303296892559732117557030489502956111965 * 10 ^ 70 +
        7843777554979459890963433366527245444032723078565661774875799898073076) * 10 ^ 70 +
        5277738610953551274133045624014363264861589557523758450811242803425339) * 10 ^ 70 +
        4103279553450047953678949584795193715761312805159552283778693580892312) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 424,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (423 - x)) = _
  rw [show 424 = 237 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 28 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_423_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_423_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_424_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (424 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (424 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_424_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (424 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_424 :
    recurrence4Scalar2Left.coeff 424 =
      ((((155018569658609261133255147974151832747509949 * 10 ^ 70 +
        9520787000143093714387949950434693679275839955621085469046428998614841) * 10 ^ 70 +
        0547769106357895459568597378502985199366549759134361150679433053138380) * 10 ^ 70 +
        4183980648506293859913151675248755569810009993059929655210975090014257) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 425,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (424 - x)) = _
  rw [show 425 = 238 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 27 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_424_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_424_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_425_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (425 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (425 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_425_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (425 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_425 :
    recurrence4Scalar2Left.coeff 425 =
      -((((42798652520939500625446795897929864600779843 * 10 ^ 70 +
        0005682841812963764554724782837621976154535595977924701202435167576646) * 10 ^ 70 +
        8635028637057856963204498095173715435786085540230769618958493069256239) * 10 ^ 70 +
        1973715814794085583290154515786819930543278201700205931786419177985405) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 426,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (425 - x)) = _
  rw [show 426 = 239 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 26 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_425_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_425_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_426_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (426 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (426 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_426_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (426 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_426 :
    recurrence4Scalar2Left.coeff 426 =
      ((((11249862868042995839094521084566353260633188 * 10 ^ 70 +
        3154349414952587016167660617070100412330054455641095863824494602607732) * 10 ^ 70 +
        4124822472783082071396431890724097262888400715919450292542186555023434) * 10 ^ 70 +
        9937485635866216575801384741706243256281861652537297776492593752351651) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 427,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (426 - x)) = _
  rw [show 427 = 240 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 25 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_426_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_426_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_427_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (427 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (427 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_427_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (427 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_427 :
    recurrence4Scalar2Left.coeff 427 =
      -((((2790426055739078974297544084916752653089904 * 10 ^ 70 +
        2592501413560355708106765783329120968022790945401058528987019464359291) * 10 ^ 70 +
        8468673612379114185213256436421727395889099820171551760416009876909909) * 10 ^ 70 +
        6827619026958562382711652226097404571445014936292182210434487016392666) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 428,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (427 - x)) = _
  rw [show 428 = 241 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 24 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_427_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_427_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_428_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (428 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (428 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_428_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (428 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_428 :
    recurrence4Scalar2Left.coeff 428 =
      ((((643582332991654987882416063042196169566690 * 10 ^ 70 +
        2113949659293866260056119518751497248534855394290842809195481556487176) * 10 ^ 70 +
        8859745135424556717215684026953567653739970256393332603165695083867607) * 10 ^ 70 +
        5331396433516935878681519225728760278007243034697068357156061053078427) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 429,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (428 - x)) = _
  rw [show 429 = 242 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 23 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_428_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_428_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_429_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (429 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (429 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_429_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (429 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_429 :
    recurrence4Scalar2Left.coeff 429 =
      -((((134286107097374431739077623108500871092372 * 10 ^ 70 +
        7729621420589808338926482643265680144175871276142396297896520622767537) * 10 ^ 70 +
        2871222747455754945884396860993315680276394935861239893278391321051849) * 10 ^ 70 +
        6390403026170575410497593950889349335387804424311764873733225319244703) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 430,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (429 - x)) = _
  rw [show 430 = 243 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 22 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_429_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_429_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_430_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (430 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (430 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_430_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (430 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_430 :
    recurrence4Scalar2Left.coeff 430 =
      ((((23811722635975634582861213912938450396355 * 10 ^ 70 +
        5206817936406745789582071988363188734572290725067963546707508087003789) * 10 ^ 70 +
        8626501344159756854346803510814671710443809544768670165312442455178048) * 10 ^ 70 +
        7327476857187388151240137872965625951729277955256585492831366280571455) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 431,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (430 - x)) = _
  rw [show 431 = 244 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 21 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_430_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_430_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_431_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (431 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (431 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_431_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (431 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_431 :
    recurrence4Scalar2Left.coeff 431 =
      -((((2895718397612728902922043096217944037265 * 10 ^ 70 +
        0850455722476671382031856865647820192420395581088002375168221526315030) * 10 ^ 70 +
        9673537203615364572590502950682393064175447962574892301053479428076717) * 10 ^ 70 +
        7665378518995707012829497908287587802084629044776602448864399195751432) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 432,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (431 - x)) = _
  rw [show 432 = 245 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 20 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_431_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_431_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_432_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (432 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (432 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_432_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (432 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_432 :
    recurrence4Scalar2Left.coeff 432 =
      -((((127409525162271904890740931711636460177 * 10 ^ 70 +
        0475852437815620141616783232858508746863899797023286932597717466078070) * 10 ^ 70 +
        5104650466971171483441514170116851675903617836253130348433787031519490) * 10 ^ 70 +
        8668043626834260202318769445156297558985293807477550482389951363004037) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 433,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (432 - x)) = _
  rw [show 433 = 246 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 19 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_432_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_432_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
