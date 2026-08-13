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

private theorem recurrence4Scalar2Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (358 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (358 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_358 :
    recurrence4Scalar2Left.coeff 358 =
      (((((12043 * 10 ^ 70 +
        6556518629185866869501035774644703588126853730127602773433150891344950) * 10 ^ 70 +
        6221097494299367500788902185686813152520538147623196826277446801393198) * 10 ^ 70 +
        7128265260743550268223125817285502597788024279696718259325141166700404) * 10 ^ 70 +
        9736614336906760950662460494334116265508374074560393571575239684262124) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 359,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (358 - x)) = _
  rw [show 359 = 172 +
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
    rw [show 59 = 29 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (359 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (359 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_359 :
    recurrence4Scalar2Left.coeff 359 =
      -(((((5211 * 10 ^ 70 +
        5783449676338926003671025949423109776620569834192310918716042959419761) * 10 ^ 70 +
        6733759921425597107504417077932855622539705197822247312059584499873843) * 10 ^ 70 +
        3183688369903599110656011573902367000882272210388839371457495231737720) * 10 ^ 70 +
        0274576872609415898054943841711285137527647311180343664870216200195120) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 360,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (359 - x)) = _
  rw [show 360 = 173 +
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
    rw [show 59 = 28 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (360 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (360 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_360 :
    recurrence4Scalar2Left.coeff 360 =
      (((((2295 * 10 ^ 70 +
        5017403577585325968997587267835639510921476134134937890674127000271525) * 10 ^ 70 +
        0710669389098572363479702337235768982436845282050721021988760563844468) * 10 ^ 70 +
        4983757696670666767648224690883477999522820963810474823980244272814445) * 10 ^ 70 +
        1656784918600268077407247158793829112843899225327658204598453219268695) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 361,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (360 - x)) = _
  rw [show 361 = 174 +
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
    rw [show 59 = 27 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (361 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (361 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_361 :
    recurrence4Scalar2Left.coeff 361 =
      -(((((1014 * 10 ^ 70 +
        7978019083690633855934541189092438799209635409078036274822612081088472) * 10 ^ 70 +
        2230489234911899651915703482283069656908531569275564924895493655745071) * 10 ^ 70 +
        3436066645181344145632299149770365949499630111689939072826594126046231) * 10 ^ 70 +
        8924909021166182266469524088791242831157556641070197014638748574655682) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 362,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (361 - x)) = _
  rw [show 362 = 175 +
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
    rw [show 59 = 26 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (362 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (362 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_362 :
    recurrence4Scalar2Left.coeff 362 =
      (((((445 * 10 ^ 70 +
        2741306940391640936443187047047986364583304743296181734549318809601295) * 10 ^ 70 +
        4318807172365869449889001421689267795330471009072835683894262669271517) * 10 ^ 70 +
        8817002538248207661147667002962030328257733107439152730658322036026815) * 10 ^ 70 +
        0656212200455836257338957266941622650974701062326154512771855881509388) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 363,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (362 - x)) = _
  rw [show 363 = 176 +
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
    rw [show 59 = 25 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (363 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (363 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_363 :
    recurrence4Scalar2Left.coeff 363 =
      -(((((192 * 10 ^ 70 +
        3849661992547868419115317086099079828883706109385286164938981736486937) * 10 ^ 70 +
        2526622803563029499974508615911859772348283492973937463845702477972250) * 10 ^ 70 +
        4622855130995696818649207436881280968891751438623551109278898515101975) * 10 ^ 70 +
        2104356938620115276189366289960009931651919458700119669202805775656356) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 364,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (363 - x)) = _
  rw [show 364 = 177 +
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
    rw [show 59 = 24 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (364 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (364 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_364 :
    recurrence4Scalar2Left.coeff 364 =
      (((((81 * 10 ^ 70 +
        4078339967504007025613402986351200055623605261736528480012737804743709) * 10 ^ 70 +
        4483196694852692373534817578931546302592703185843090725011331482023178) * 10 ^ 70 +
        3778625026076295692550605895207637119367287037350471197751349805671632) * 10 ^ 70 +
        1055231874087363795547465973162723701637892886823349399602504969885890) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 365,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (364 - x)) = _
  rw [show 365 = 178 +
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
    rw [show 59 = 23 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (365 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (365 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_365 :
    recurrence4Scalar2Left.coeff 365 =
      -(((((33 * 10 ^ 70 +
        6119854956930676053467310186540363294830532928252158921031942006626845) * 10 ^ 70 +
        7202474460510206071652097263330703600521137451052875805839036552733691) * 10 ^ 70 +
        9025736547435331906314721948413001674632845013314709722570770291946564) * 10 ^ 70 +
        5330706549034378209466606872004476784230228804941187705171944382769190) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 366,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (365 - x)) = _
  rw [show 366 = 179 +
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
    rw [show 59 = 22 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (366 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (366 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_366 :
    recurrence4Scalar2Left.coeff 366 =
      (((((13 * 10 ^ 70 +
        5031031152509680885076665397952208769869152265085176599007357457410167) * 10 ^ 70 +
        6025790413275275051335936082828369511514313525384947832284053626726709) * 10 ^ 70 +
        1619706198737147020597589565358352223773155177051683260079473977163430) * 10 ^ 70 +
        5157023591510315900823476631926158682826689843030109990303745316567536) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 367,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (366 - x)) = _
  rw [show 367 = 180 +
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
    rw [show 59 = 21 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (367 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (367 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_367 :
    recurrence4Scalar2Left.coeff 367 =
      -(((((5 * 10 ^ 70 +
        2650758452128127990591477210079870008921422030434133610398439724935005) * 10 ^ 70 +
        4875759883757176667125304634578093779142894345720632152646653856964275) * 10 ^ 70 +
        9094437294095989323356658524353553760444972480092007255738767633424026) * 10 ^ 70 +
        2239973372937932376653249930291508369928439082290613854866232057965906) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 368,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (367 - x)) = _
  rw [show 368 = 181 +
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
    rw [show 59 = 20 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (368 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (368 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_368 :
    recurrence4Scalar2Left.coeff 368 =
      (((((1 * 10 ^ 70 +
        9872944010922312640049805449741488881686473548242190902452667585912351) * 10 ^ 70 +
        0431524830827308311859621119333237231749794716377082388572160057288763) * 10 ^ 70 +
        0092985510879364924665460900285979889091144189333148713401623309807804) * 10 ^ 70 +
        4965824740768683699796343149474145611857940221329754854252288261356353) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 369,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (368 - x)) = _
  rw [show 369 = 182 +
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
    rw [show 59 = 19 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (369 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (369 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_369 :
    recurrence4Scalar2Left.coeff 369 =
      -((((7237627219924316758240999093847130562675512904442786661488826066073317 * 10 ^ 70 +
        9844339800499341574789052924578807171394900970027547305578037854761776) * 10 ^ 70 +
        7153320071409854778521751038736849271615139741074372078342394438614478) * 10 ^ 70 +
        0233085533087188062966432564092811651940738670473304565663471917510515) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 370,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (369 - x)) = _
  rw [show 370 = 183 +
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
    rw [show 59 = 18 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (370 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (370 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_370 :
    recurrence4Scalar2Left.coeff 370 =
      ((((2532107001458735218233426333418257551562942610458790829506328832251209 * 10 ^ 70 +
        7883261115552533682897812289813947194307130641150924032070265915621310) * 10 ^ 70 +
        1525054218198579930904017471706339233637652116030080756869191314672343) * 10 ^ 70 +
        1414646718776183755224320110622649125363981457621359411631474264862341) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 371,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (370 - x)) = _
  rw [show 371 = 184 +
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
    rw [show 59 = 17 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (371 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (371 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_371 :
    recurrence4Scalar2Left.coeff 371 =
      -((((845442830063413075816568544619864117975339135820966606651426004511198 * 10 ^ 70 +
        2602863205789381369285718354558999456185606610988135721949766543246295) * 10 ^ 70 +
        7745901748340681741024682064025945866414211663158859320735707356891700) * 10 ^ 70 +
        3923271155719686037041484362327253810500807621140466725327008639802688) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 372,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (371 - x)) = _
  rw [show 372 = 185 +
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
    rw [show 59 = 16 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (372 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (372 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_372 :
    recurrence4Scalar2Left.coeff 372 =
      ((((266624086400572999466762802171288119734871953662569997232675637371919 * 10 ^ 70 +
        8635605916535715253743955725509130051261021263946753961439263937673222) * 10 ^ 70 +
        6818178253761103234732272941548349500104779396482089270886694080381021) * 10 ^ 70 +
        0541280819781116805137673046038407274939870750140616460556385748034755) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 373,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (372 - x)) = _
  rw [show 373 = 186 +
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
    rw [show 59 = 15 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (373 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (373 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_373 :
    recurrence4Scalar2Left.coeff 373 =
      -((((77993153632536626698132318789354820438086140147700221283179306289541 * 10 ^ 70 +
        6104388011871569511173673788214496577079269220680590320350714044181624) * 10 ^ 70 +
        9048952641639761676248193630978276992417922063807681274220236041019681) * 10 ^ 70 +
        5359399106566570639021349011774671580273068290678255695253454264726756) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 374,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (373 - x)) = _
  rw [show 374 = 187 +
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
    rw [show 59 = 14 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (374 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (374 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_374 :
    recurrence4Scalar2Left.coeff 374 =
      ((((20402058429805995741326034053663442433163762638152704925343951345434 * 10 ^ 70 +
        7612654696045746960024928909384207805643046644885627311109203032258489) * 10 ^ 70 +
        4960483949565711033794310187377292678090284083118687234289570780803053) * 10 ^ 70 +
        2858436258877479354764842032331496192181194715461099899884695490874644) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 375,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (374 - x)) = _
  rw [show 375 = 188 +
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
    rw [show 59 = 13 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (375 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (375 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_375 :
    recurrence4Scalar2Left.coeff 375 =
      -((((4340494595323872933405731236412059215489818133412365210975447469390 * 10 ^ 70 +
        7534756628951527008351165765278097248315830720381980552299056587442574) * 10 ^ 70 +
        4494981316551390013427055889072382741386028976154831485799666137705793) * 10 ^ 70 +
        2808918833994892054094194137081322417625235429396231682816202703588956) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 376,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (375 - x)) = _
  rw [show 376 = 189 +
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
    rw [show 59 = 12 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (376 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (376 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_376 :
    recurrence4Scalar2Left.coeff 376 =
      ((((474835163355693534283140736112441330939213135558169069111753726072 * 10 ^ 70 +
        6443563528407296598750615119733101142206689195900749792998077259071023) * 10 ^ 70 +
        5786043666434337619129342047892776436186764805816792851223155797070252) * 10 ^ 70 +
        5316315302003189268526526085655099137164746396804404505080644216474066) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 377,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (376 - x)) = _
  rw [show 377 = 190 +
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
    rw [show 59 = 11 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (377 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (377 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_377 :
    recurrence4Scalar2Left.coeff 377 =
      ((((192501557472663112437242973522048199753360588458535533020615330303 * 10 ^ 70 +
        6707585182446764172379488969781912350704891934642435561054079690621398) * 10 ^ 70 +
        8145996032611948038227766659438211549273651065015723144663000236629258) * 10 ^ 70 +
        7001412334851814534077417014733800196804453199839857261685737902591442) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 378,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (377 - x)) = _
  rw [show 378 = 191 +
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
    rw [show 59 = 10 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (378 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (378 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_378 :
    recurrence4Scalar2Left.coeff 378 =
      -((((179751563990354565683951421900542797030741574926043619570717615274 * 10 ^ 70 +
        3335311186787572088270980624663552937600095487538728126737691614131609) * 10 ^ 70 +
        9145649224162915951961323628208841717096026780519267747105053791795480) * 10 ^ 70 +
        7511095467854256704842548640726425288681761418433856079650320382764595) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 379,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (378 - x)) = _
  rw [show 379 = 192 +
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
    rw [show 59 = 9 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (379 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (379 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_379 :
    recurrence4Scalar2Left.coeff 379 =
      ((((94089626649466921790199605853446777730752719464261377265272035485 * 10 ^ 70 +
        9488828765762464953444900914057690778348594163213960277292878897888234) * 10 ^ 70 +
        9282421753213986763232373393996374002050927610820147957267594131668165) * 10 ^ 70 +
        4756859859936874087745248375858815261020886286880613567949656691034530) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 380,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (379 - x)) = _
  rw [show 380 = 193 +
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
    rw [show 59 = 8 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (380 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (380 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_380 :
    recurrence4Scalar2Left.coeff 380 =
      -((((39964513516020553125674109062967332874300021919390173970408172948 * 10 ^ 70 +
        5700906607580028422519978163702835367894256968521201214262261692254988) * 10 ^ 70 +
        3551340471543154866670325169965504915535152060798031875883923390723881) * 10 ^ 70 +
        6310890606239748203839640482162927502269131597788118142709823554032587) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 381,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (380 - x)) = _
  rw [show 381 = 194 +
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
    rw [show 59 = 7 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (381 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (381 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_381 :
    recurrence4Scalar2Left.coeff 381 =
      ((((14848382274503983674175699377434665843394195652975028826933129746 * 10 ^ 70 +
        1850366721282398402001718189730906455271559244402248764715598138049562) * 10 ^ 70 +
        0408510122637230977339211419268040309268153787792870282449552984152876) * 10 ^ 70 +
        7618426632079211494880629542242499929230371858387251820639207575437956) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 382,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (381 - x)) = _
  rw [show 382 = 195 +
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
    rw [show 59 = 6 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_381_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
