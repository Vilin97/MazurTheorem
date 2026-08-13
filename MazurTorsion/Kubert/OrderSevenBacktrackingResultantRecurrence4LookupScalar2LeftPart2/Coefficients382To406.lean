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

private theorem recurrence4Scalar2Left_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (382 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (382 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_382 :
    recurrence4Scalar2Left.coeff 382 =
      -((((4901743913621891470863522628085701024178795250777890221482128481 * 10 ^ 70 +
        2452105975059090113561429655061254547930950737211626117285238995127148) * 10 ^ 70 +
        0105568248223159202198818886617524657969839539359992051553201736572170) * 10 ^ 70 +
        5157715460114435887125092313919226560051202189227732039942550863374416) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 383,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (382 - x)) = _
  rw [show 383 = 196 +
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
    rw [show 59 = 5 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_382_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_383_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (383 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (383 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_383_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (383 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_383 :
    recurrence4Scalar2Left.coeff 383 =
      ((((1408818476863165013156881811703669849491557056155596775717224860 * 10 ^ 70 +
        1630140159185983801130057041123529150082729323045273208410183035500364) * 10 ^ 70 +
        3099051350250834861785044546161509124663950420412996150491015811108573) * 10 ^ 70 +
        6899072844220034900994403159195547241337999602861645103449115303439371) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 384,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (383 - x)) = _
  rw [show 384 = 197 +
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
    rw [show 59 = 4 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_383_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_383_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_384_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (384 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (384 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_384_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (384 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_384 :
    recurrence4Scalar2Left.coeff 384 =
      -((((322161170039024829375794824632417942313110693429320701527708624 * 10 ^ 70 +
        5021353163574347016816075377987236251695448239341417720454574841619361) * 10 ^ 70 +
        7475156026658584841498331633597154575041779113946346186018189640961004) * 10 ^ 70 +
        4355878137809737034474372611389543744342577161144183045170517545203846) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 385,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (384 - x)) = _
  rw [show 385 = 198 +
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
    rw [show 59 = 3 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_384_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_384_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_385_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (385 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (385 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_385_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (385 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_385 :
    recurrence4Scalar2Left.coeff 385 =
      ((((35033478559764422255944047726753303951770931661180525538952639 * 10 ^ 70 +
        2644193816910550141754269804634994159388251248415590692137624909990566) * 10 ^ 70 +
        6690526030271116469940496159411177706743719331272051795700932277057247) * 10 ^ 70 +
        4757232541860961756745781689973905829596495948123185714764454082623838) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 386,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (385 - x)) = _
  rw [show 386 = 199 +
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
    rw [show 59 = 2 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_385_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_385_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_386_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (386 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (386 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_386_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (386 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_386 :
    recurrence4Scalar2Left.coeff 386 =
      ((((19282666879695887937698758426957480941962872166179735334532521 * 10 ^ 70 +
        1775841272941020677361367510351591620283659347886623664288460727299947) * 10 ^ 70 +
        5769034487355971032399117331378435923129209831641227536534004866804418) * 10 ^ 70 +
        2265974805645025492487723785883582621823103114962090886968888981458012) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 387,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (386 - x)) = _
  rw [show 387 = 200 +
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
    rw [show 59 = 1 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_386_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_386_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_387_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (387 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (387 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_387_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (387 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_387 :
    recurrence4Scalar2Left.coeff 387 =
      -((((18560943311116612265638138801107958759732820644605754782795985 * 10 ^ 70 +
        8982073409837647844576862444753110360302844296475385862049428009060086) * 10 ^ 70 +
        7298865202053337744217166322576367362033151803114712900766311546551450) * 10 ^ 70 +
        5800339450534517243692861231725266027331964343820083333321928913978197) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 388,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (387 - x)) = _
  rw [show 388 = 201 +
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
  rw [recurrence4Scalar2Left_coeff_387_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_387_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_388_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (388 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (388 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_388_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (388 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_388 :
    recurrence4Scalar2Left.coeff 388 =
      ((((10633804283071655413693847500729009544011689024833846130975729 * 10 ^ 70 +
        5073934649011430125528654566833134177123146774989043300824664791725334) * 10 ^ 70 +
        5972620209763572041300569216314905702503656586925135725488280360191175) * 10 ^ 70 +
        3629057872186195841772652336673129004508080860337935327098940675948091) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 389,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (388 - x)) = _
  rw [show 389 = 202 +
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
    rw [show 91 = 31 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_388_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_388_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_389_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (389 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (389 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_389_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (389 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_389 :
    recurrence4Scalar2Left.coeff 389 =
      -((((5082001605922062495167876507369403564694849832278268308902274 * 10 ^ 70 +
        3194820553929379206663447358945523433924879434614002288490043720681372) * 10 ^ 70 +
        9826270543671501334516917549528375797981158210251205337402073676581662) * 10 ^ 70 +
        0565333192852117820519931236465153219922731920803016078385715464560511) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 390,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (389 - x)) = _
  rw [show 390 = 203 +
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
    rw [show 91 = 30 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_389_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_389_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_390_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (390 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (390 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_390_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (390 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_390 :
    recurrence4Scalar2Left.coeff 390 =
      ((((2195829221213345794558696493451130734158184445582251093906395 * 10 ^ 70 +
        4309811681659772900770879988285133433810796104134355193439657450885190) * 10 ^ 70 +
        3356121065051855484638095887186240770777818868352169629608642719513861) * 10 ^ 70 +
        8096565506175907931565785606471530901709993556754050818787418936775607) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 391,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (390 - x)) = _
  rw [show 391 = 204 +
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
    rw [show 91 = 29 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_390_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_390_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_391_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (391 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (391 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_391_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (391 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_391 :
    recurrence4Scalar2Left.coeff 391 =
      -((((885497463292703775168307995326555359115124946055047051219147 * 10 ^ 70 +
        8250311885031262920170962063936976764997975395175533220882940470761655) * 10 ^ 70 +
        1369507363643012056265840573372304523112965965250548417930789058185600) * 10 ^ 70 +
        0898894070856778060082856761897752435257478613941388831649919129076329) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 392,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (391 - x)) = _
  rw [show 392 = 205 +
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
    rw [show 91 = 28 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_391_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_391_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_392_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (392 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (392 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_392_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (392 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_392 :
    recurrence4Scalar2Left.coeff 392 =
      ((((338357486455706244471177393019056959737328208550157187072168 * 10 ^ 70 +
        1007195258881656019672047038191031984527591076620212094454928070380598) * 10 ^ 70 +
        6382766487234030627546865121768070739172618814636058217011471077076579) * 10 ^ 70 +
        1121620851693590897249239810048677969105002508772465217956512772394279) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 393,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (392 - x)) = _
  rw [show 393 = 206 +
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
    rw [show 91 = 27 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_392_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_392_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_393_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (393 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (393 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_393_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (393 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_393 :
    recurrence4Scalar2Left.coeff 393 =
      -((((123427432442073283870315777994179012473590223962047865768601 * 10 ^ 70 +
        2070710432092750516697906943496957154607312631632038195794270490769015) * 10 ^ 70 +
        8232900565260277960121459712621822171834957292469678360684727987709149) * 10 ^ 70 +
        5939157091356672987450102718418246561970440556810383300603396835776690) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 394,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (393 - x)) = _
  rw [show 394 = 207 +
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
    rw [show 91 = 26 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_393_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_393_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_394_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (394 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (394 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_394_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (394 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_394 :
    recurrence4Scalar2Left.coeff 394 =
      ((((43114634979088880187485216662855919516109210621617865200757 * 10 ^ 70 +
        0179248790743748389879052147186370467712475848410031763880815886335361) * 10 ^ 70 +
        5031358805732488640368866504616080875687602254712877440637639820509106) * 10 ^ 70 +
        1951019935372424780649340031690580308164434672135678367655049220601977) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 395,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (394 - x)) = _
  rw [show 395 = 208 +
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
    rw [show 91 = 25 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_394_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_394_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_395_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (395 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (395 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_395_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (395 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_395 :
    recurrence4Scalar2Left.coeff 395 =
      -((((14419597448581972321927068006744067692866616042800623106765 * 10 ^ 70 +
        6592016943301601467316736534063605859951577632439862733347028274557242) * 10 ^ 70 +
        7006878232424658947407388697455479607489869681214914990809425372377097) * 10 ^ 70 +
        7880717225067899426708038974093735550473616704820416380006714296081179) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 396,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (395 - x)) = _
  rw [show 396 = 209 +
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
    rw [show 91 = 24 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_395_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_395_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_396_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (396 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (396 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_396_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (396 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_396 :
    recurrence4Scalar2Left.coeff 396 =
      ((((4602745526014871118348435449396977781143644609484157332506 * 10 ^ 70 +
        6908930346840197662277737096551187307471257635067389992138400100433692) * 10 ^ 70 +
        1490591208070299323949109735742516539951216461852928885488022939018712) * 10 ^ 70 +
        7686130764027758422362691325471738156742354497426863808082928854283908) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 397,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (396 - x)) = _
  rw [show 397 = 210 +
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
    rw [show 91 = 23 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_396_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_396_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_397_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (397 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (397 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_397_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (397 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_397 :
    recurrence4Scalar2Left.coeff 397 =
      -((((1392428690440330616754750644062279438172583830310313903958 * 10 ^ 70 +
        3828754965712247916924926610676868134389941053970509374079590163733290) * 10 ^ 70 +
        1015947315542613819574502665890756136236635751666590675519889023832033) * 10 ^ 70 +
        3693646305076194409835037720655693492703252095116866979249670083754286) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 398,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (397 - x)) = _
  rw [show 398 = 211 +
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
    rw [show 91 = 22 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_397_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_397_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_398_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (398 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (398 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_398_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (398 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_398 :
    recurrence4Scalar2Left.coeff 398 =
      ((((393960466887556554665865765423914470034950063250558153529 * 10 ^ 70 +
        1966871201378146213279841866460282501904208044040643812140431340373074) * 10 ^ 70 +
        6342836938350100557921840933464906766727710942344342640269929104691357) * 10 ^ 70 +
        5509471966737002474075236049739236154195016043502858625944343927246903) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 399,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (398 - x)) = _
  rw [show 399 = 212 +
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
    rw [show 91 = 21 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_398_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_398_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_399_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (399 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (399 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_399_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (399 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_399 :
    recurrence4Scalar2Left.coeff 399 =
      -((((101541877205487224690355101032910082832795399811076590530 * 10 ^ 70 +
        0458633433493952225675084732446728694346929669655042963639576289238415) * 10 ^ 70 +
        1401674710006058958089385679433859349176875858367787984146531164124260) * 10 ^ 70 +
        4754158609979128279183391684073325990521827194081163852738765420819066) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 400,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (399 - x)) = _
  rw [show 400 = 213 +
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
    rw [show 91 = 20 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_399_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_399_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_400_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (400 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (400 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_400_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (400 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_400 :
    recurrence4Scalar2Left.coeff 400 =
      ((((22422738024341612500770933710728882751389230548837969666 * 10 ^ 70 +
        2155195859158747019861969168669386461000573553389483334328032642166338) * 10 ^ 70 +
        2889005077123068135856951774279258021638343126996216373456534299307772) * 10 ^ 70 +
        4139082680269169919977702154142832495885302318981016791912428481756422) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 401,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (400 - x)) = _
  rw [show 401 = 214 +
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
    rw [show 91 = 19 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_400_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_400_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_401_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (401 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (401 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_401_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (401 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_401 :
    recurrence4Scalar2Left.coeff 401 =
      -((((3432979352296467693474476537889009338632239965147358544 * 10 ^ 70 +
        3209373367700255009675529821052173102874455590658929108535415783813731) * 10 ^ 70 +
        8333389556329640303528955028585764665536775230410486757458286013143557) * 10 ^ 70 +
        5206533516717372251359922004913456510571498207707185570300930430758284) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 402,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (401 - x)) = _
  rw [show 402 = 215 +
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
    rw [show 91 = 18 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_401_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_401_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_402_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (402 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (402 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_402_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (402 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_402 :
    recurrence4Scalar2Left.coeff 402 =
      -((((180433339891394026992461656557340444219120102475273068 * 10 ^ 70 +
        4925670333837409068375050779352663766530610936076478134413378745233772) * 10 ^ 70 +
        5247518793565782662762538687391776322446820032081977757596684378994648) * 10 ^ 70 +
        5589483458145206905107838555963809956450603538323063044943528766937470) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 403,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (402 - x)) = _
  rw [show 403 = 216 +
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
    rw [show 91 = 17 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_402_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_402_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_403_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (403 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (403 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_403_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (403 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_403 :
    recurrence4Scalar2Left.coeff 403 =
      ((((460434944769605000034817652155602361875932502712365765 * 10 ^ 70 +
        0206652547356444078983480708261202814504147574995432027452335931245603) * 10 ^ 70 +
        3743630870321094259474827738275121339180419374404449946013252888079023) * 10 ^ 70 +
        2856575310972205503252628181420151118863481518571759933347116338477785) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 404,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (403 - x)) = _
  rw [show 404 = 217 +
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
    rw [show 91 = 16 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_403_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_403_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_404_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (404 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (404 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_404_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (404 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_404 :
    recurrence4Scalar2Left.coeff 404 =
      -((((262847440013764398859794384401150840245814926130109308 * 10 ^ 70 +
        7412010644688753811442946241677212189730105157996141801768997249456792) * 10 ^ 70 +
        1233453940548675691806046946303481052050442280207699517813704450984350) * 10 ^ 70 +
        0543593886089255482116802071407464278439112830530582977105218323683628) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 405,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (404 - x)) = _
  rw [show 405 = 218 +
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
    rw [show 91 = 15 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_404_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_404_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_405_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (405 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (405 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_405_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (405 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_405 :
    recurrence4Scalar2Left.coeff 405 =
      ((((113306095038723238476763957304084271070844144806919817 * 10 ^ 70 +
        4195828324694562218195477966686084352683614425848242755305459535532052) * 10 ^ 70 +
        8335660394844116286853309697140785349447960283989443089865729200108723) * 10 ^ 70 +
        1255850589827842142983655183027737424287186112169980562767334032531755) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 406,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (405 - x)) = _
  rw [show 406 = 219 +
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
    rw [show 91 = 14 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_405_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_405_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_406_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (406 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (406 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_406_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (406 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_406 :
    recurrence4Scalar2Left.coeff 406 =
      -((((42147259253345951767882376652022006296697035641401348 * 10 ^ 70 +
        6950604529429255135357891086928849044149437636098829795154789619971846) * 10 ^ 70 +
        0661614757351416434344237125998516199772689775736755079653343499200096) * 10 ^ 70 +
        2258910550247949515781247744524352266108399514109817597367146625528168) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 407,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (406 - x)) = _
  rw [show 407 = 220 +
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
    rw [show 91 = 13 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_406_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_406_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
