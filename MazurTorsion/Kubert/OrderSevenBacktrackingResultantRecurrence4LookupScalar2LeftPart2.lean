/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_433_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (433 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (433 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_433_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (433 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_433 :
    recurrence4Scalar2Left.coeff 433 =
      ((((244857973921286128882791047080303530771 * 10 ^ 70 +
        3643603392798810437252986679496734048858010057772849715353325830194864) * 10 ^ 70 +
        9395858937915070980090858719875929318231044168839495529890638973222420) * 10 ^ 70 +
        6729038284752113022364515775617409464301365046981242193379766290156991) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 434,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (433 - x)) = _
  rw [show 434 = 247 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 18 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_433_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_433_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_434_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (434 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (434 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_434_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (434 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_434 :
    recurrence4Scalar2Left.coeff 434 =
      -((((108770027275399426401931260369832576951 * 10 ^ 70 +
        7794409692855535966183875352406638918978071158230306279613641348905657) * 10 ^ 70 +
        6756788542988497490839151479470168814201710536855365425445069261116929) * 10 ^ 70 +
        7757105375398512780750885760083207342487537668949416552986384318005135) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 435,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (434 - x)) = _
  rw [show 435 = 248 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 17 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_434_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_434_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_435_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (435 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (435 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_435_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (435 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_435 :
    recurrence4Scalar2Left.coeff 435 =
      ((((36390089365785479015045692416453643188 * 10 ^ 70 +
        5203193404579713167530785937493767479438911421446003944391027569201998) * 10 ^ 70 +
        8013200759830146911646481728103773561740670762831064422718820414777731) * 10 ^ 70 +
        1301400858588347946859237734126410242877584003897524894466070735865815) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 436,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (435 - x)) = _
  rw [show 436 = 249 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 16 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_435_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_435_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_436_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (436 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (436 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_436_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (436 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_436 :
    recurrence4Scalar2Left.coeff 436 =
      -((((10507236258510291726465354828124268781 * 10 ^ 70 +
        9813609142627558688552402465248899017650152840757730133417997049814357) * 10 ^ 70 +
        2978064772845870887666273879365631326894019134778560063074046522373764) * 10 ^ 70 +
        4184917650136564045947132037673979708994640088498778888533165401585322) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 437,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (436 - x)) = _
  rw [show 437 = 250 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 15 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_436_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_436_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_437_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (437 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (437 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_437_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (437 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_437 :
    recurrence4Scalar2Left.coeff 437 =
      ((((2737135914561965601530245204498934309 * 10 ^ 70 +
        6069114745368280056603194150257405828735332427837133961473177687778165) * 10 ^ 70 +
        6365364589371818807975571411588532249450668934717993222035795283301566) * 10 ^ 70 +
        4028159804728396727755776541117140318114790117756266796868702020372776) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 438,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (437 - x)) = _
  rw [show 438 = 251 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 14 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_437_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_437_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_438_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (438 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (438 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_438_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (438 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_438 :
    recurrence4Scalar2Left.coeff 438 =
      -((((655559400858226313292605653768815265 * 10 ^ 70 +
        6584240500416062464586115892015282407245812007087094576608222394356411) * 10 ^ 70 +
        2640344714142582777450063867315965697677439208120452267664510149405974) * 10 ^ 70 +
        5718126615919028116101917078661384772569901608266819529674338711254728) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 439,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (438 - x)) = _
  rw [show 439 = 252 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 13 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_438_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_438_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_439_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (439 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (439 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_439_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (439 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_439 :
    recurrence4Scalar2Left.coeff 439 =
      ((((145602557772450920258604809693012914 * 10 ^ 70 +
        3785761936534684596683724854693228271008685643331447660894433601089293) * 10 ^ 70 +
        4484417602739051491499752511091749968018284986688255701683585275650117) * 10 ^ 70 +
        1607711969635203654445830973928602158024267425013856999370232655445682) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 440,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (439 - x)) = _
  rw [show 440 = 253 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 12 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_439_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_439_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_440_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (440 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (440 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_440_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (440 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_440 :
    recurrence4Scalar2Left.coeff 440 =
      -((((30086290218814662587956104952054903 * 10 ^ 70 +
        8472928923867647910154310808342797944094540400219320298008743595138866) * 10 ^ 70 +
        1065225915164592237756179201707785347083143732084687208222705837025378) * 10 ^ 70 +
        6313938470544652389732480798014344772514853232930916891031657536189963) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 441,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (440 - x)) = _
  rw [show 441 = 254 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 11 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_440_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_440_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_441_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (441 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (441 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_441_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (441 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_441 :
    recurrence4Scalar2Left.coeff 441 =
      ((((5781568149269423938867536152279338 * 10 ^ 70 +
        9517053505847482506066775326402202821613165756253861519898230680115625) * 10 ^ 70 +
        9393154049144597425882689513141097184255466261240869561813668788092459) * 10 ^ 70 +
        9496401147058651529138392397347984977286299249975386987304017642322771) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 442,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (441 - x)) = _
  rw [show 442 = 255 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 10 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_441_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_441_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_442_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (442 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (442 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_442_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (442 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_442 :
    recurrence4Scalar2Left.coeff 442 =
      -((((1029489477725073053895473184963298 * 10 ^ 70 +
        9362050127693988419486261080631317948663268985258898855234244945696371) * 10 ^ 70 +
        6536150925415534719400142357445927083967826199541687736266366876742870) * 10 ^ 70 +
        1983343180045386012335427625499806332718199052384007585415329188748461) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 443,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (442 - x)) = _
  rw [show 443 = 256 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 9 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_442_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_442_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_443_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (443 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (443 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_443_suffix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (443 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_443 :
    recurrence4Scalar2Left.coeff 443 =
      ((((168572755922375647841859210333753 * 10 ^ 70 +
        9340005217287166224867320989404283799961135146720986485246850865261696) * 10 ^ 70 +
        3605765832426339526121382345334496189656984759433678812109078655477468) * 10 ^ 70 +
        0180455053055888267963263252995802819145765117585701591185117573711779) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 444,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (443 - x)) = _
  rw [show 444 = 257 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 8 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_443_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_443_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_444_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (444 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (444 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_444_suffix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (444 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_444 :
    recurrence4Scalar2Left.coeff 444 =
      -((((25029659532904333649476350978613 * 10 ^ 70 +
        6105082933457370051527697800765194308349885493368970232542077465772712) * 10 ^ 70 +
        1546399727006276437279945216674477137511167339567627959793132395226100) * 10 ^ 70 +
        2712806076828690650239104859057542611392389234390456142336733269775958) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 445,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (444 - x)) = _
  rw [show 445 = 258 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 7 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_444_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_444_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_445_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (445 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (445 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_445_suffix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (445 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_445 :
    recurrence4Scalar2Left.coeff 445 =
      ((((3280242475819258281657725471360 * 10 ^ 70 +
        7580503205311419255083746137833385764612866073952295853819928814054520) * 10 ^ 70 +
        0607078538867935197666004973162096382372386818440769506441189170536224) * 10 ^ 70 +
        3417823883751788969246719433100994645842926293458924378580230107334940) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 446,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (445 - x)) = _
  rw [show 446 = 259 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 6 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_445_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_445_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_446_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (446 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (446 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_446_suffix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (446 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_446 :
    recurrence4Scalar2Left.coeff 446 =
      -((((356874590095574098078731083728 * 10 ^ 70 +
        4557062487353632587142892975537569828305994413190773987024144430328633) * 10 ^ 70 +
        5650069375852594905093166104063286229673349209297271604829122665519641) * 10 ^ 70 +
        7076200780895418976738683482114971460810650949733021311897675720134633) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 447,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (446 - x)) = _
  rw [show 447 = 260 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 5 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_446_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_446_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_447_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (447 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (447 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_447_suffix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (447 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_447 :
    recurrence4Scalar2Left.coeff 447 =
      ((((26279921571167459537796825670 * 10 ^ 70 +
        1606652562477943229816438703956620800692394292089258969884273971634424) * 10 ^ 70 +
        6397510894983794900463026628264148512695362969329893985218938834522049) * 10 ^ 70 +
        0990934723888325887082010114926847034937052153226382874870772214274358) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 448,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (447 - x)) = _
  rw [show 448 = 261 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 4 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_447_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_447_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_448_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (448 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (448 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_448_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (448 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_448 :
    recurrence4Scalar2Left.coeff 448 =
      ((((479697964311174565542602172 * 10 ^ 70 +
        3783199075403823121245281125732660615961365773001611976642666981630487) * 10 ^ 70 +
        5865650271267530593793783947303778295145770774938881346550186339048380) * 10 ^ 70 +
        8301917531988218879121367289189045667941937525379385991571543727814226) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 449,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (448 - x)) = _
  rw [show 449 = 262 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 3 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_448_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_448_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_449_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (449 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (449 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_449_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (449 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_449 :
    recurrence4Scalar2Left.coeff 449 =
      -((((656133061299634177993419894 * 10 ^ 70 +
        5998129961111324247985337496965544639163758595867185760066552991529269) * 10 ^ 70 +
        3543626271952447749742211340569333698256188616538598843943105613592893) * 10 ^ 70 +
        7061703571086828982643416240857540829226227197809589144567220299389826) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 450,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (449 - x)) = _
  rw [show 450 = 263 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 2 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_449_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_449_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_450_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (450 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (450 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_450_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (450 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_450 :
    recurrence4Scalar2Left.coeff 450 =
      ((((157092477577848120427454062 * 10 ^ 70 +
        5950925936388784920134300102095054841997306471239060564537253971712701) * 10 ^ 70 +
        4272577961086020118106026818386726962140050397098121026527860242629848) * 10 ^ 70 +
        6379386569858144525108677654612142764097672359632789401735321053899079) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 451,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (450 - x)) = _
  rw [show 451 = 264 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 1 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_450_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_450_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_451_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (451 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (451 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_451_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (451 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_451 :
    recurrence4Scalar2Left.coeff 451 =
      -((((26610476783237604383142834 * 10 ^ 70 +
        5515186227201519897583964653594149397701584912897089389819745016297960) * 10 ^ 70 +
        2149400182123046138500819174810753272788926362287555601204613770567912) * 10 ^ 70 +
        5784729722155269302046665002485765146333027879102280812280780781973819) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 452,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (451 - x)) = _
  rw [show 452 = 265 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_451_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_451_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_452_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (452 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (452 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_452_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (452 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_452 :
    recurrence4Scalar2Left.coeff 452 =
      ((((3612475393548972481552048 * 10 ^ 70 +
        9916843114746303110162741599273444653617152505518655143147570989788190) * 10 ^ 70 +
        9579014829388419264149605702728359868237052351374944387278821835567224) * 10 ^ 70 +
        0469623625416580859464386312363742242815119416433516872242677839622349) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 453,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (452 - x)) = _
  rw [show 453 = 266 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 31 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_452_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_452_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_453_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (453 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (453 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_453_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (453 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_453 :
    recurrence4Scalar2Left.coeff 453 =
      -((((396384754952312783774800 * 10 ^ 70 +
        4618274370694882244088828074429688422839660610023959952526105213820141) * 10 ^ 70 +
        8627596164662228843062398345563677858418736526846635185678394788002291) * 10 ^ 70 +
        3446437198392789145611792014007400247142026920996702469299915286072566) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 454,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (453 - x)) = _
  rw [show 454 = 267 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 30 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_453_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_453_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_454_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (454 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (454 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_454_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (454 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_454 :
    recurrence4Scalar2Left.coeff 454 =
      ((((32535676168496441201324 * 10 ^ 70 +
        4049914642448452502919929067074521138341269987498146854937110427728780) * 10 ^ 70 +
        6291394334869141176716216704739663795280748599693237289484888318407901) * 10 ^ 70 +
        4293772439239529811179545748398056848628282823326127653254694989822000) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 455,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (454 - x)) = _
  rw [show 455 = 268 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 29 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_454_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_454_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_455_prefix_zero :
    (∑ x ∈ Finset.range 269,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (455 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (455 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_455_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (455 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_455 :
    recurrence4Scalar2Left.coeff 455 =
      -((((1255575505533262477172 * 10 ^ 70 +
        6623718473261454583919643805723285003232442236896785155133777395676271) * 10 ^ 70 +
        0285212136123907910794827569350848986161065612049705809924721485176701) * 10 ^ 70 +
        0387827117920143179258904318883446408029543709852147571949931666209784) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 456,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (455 - x)) = _
  rw [show 456 = 269 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 28 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_455_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_455_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_456_prefix_zero :
    (∑ x ∈ Finset.range 270,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (456 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (456 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_456_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (456 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_456 :
    recurrence4Scalar2Left.coeff 456 =
      -((((179836074289554000156 * 10 ^ 70 +
        8509920584764508671944286705061279822853149731913236467018993449755644) * 10 ^ 70 +
        2048442724796566060182923871992875217131204619551467898787089268169817) * 10 ^ 70 +
        6000645207262154282708711193719045285459330036592415045362581949792323) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 457,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (456 - x)) = _
  rw [show 457 = 270 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 27 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_456_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_456_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_457_prefix_zero :
    (∑ x ∈ Finset.range 271,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (457 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (457 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_457_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (457 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_457 :
    recurrence4Scalar2Left.coeff 457 =
      ((((51600506174003621026 * 10 ^ 70 +
        0097512666465292667900290705596294933224156591739109683972724285791518) * 10 ^ 70 +
        4433658588430544275991933254585261860579582992512403083835832932220250) * 10 ^ 70 +
        3707307089734486246393512960211710745396505823837980989880224166647207) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 458,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (457 - x)) = _
  rw [show 458 = 271 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 26 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_457_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_457_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_458_prefix_zero :
    (∑ x ∈ Finset.range 272,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (458 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (458 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_458_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (458 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_458 :
    recurrence4Scalar2Left.coeff 458 =
      -((((7776987944088435849 * 10 ^ 70 +
        5103199646060860379370591437701642319658387429018190283861011501615568) * 10 ^ 70 +
        5960932466954338464443942871415929026082288839177374573740926823940798) * 10 ^ 70 +
        1695439751542229515043372721372109836847612582688408517892171973038657) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 459,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (458 - x)) = _
  rw [show 459 = 272 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 25 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_458_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_458_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_459_prefix_zero :
    (∑ x ∈ Finset.range 273,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (459 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (459 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_459_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (459 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_459 :
    recurrence4Scalar2Left.coeff 459 =
      ((((873518243253726487 * 10 ^ 70 +
        4756829098503031195142832185527750842938340890203895541586222338386137) * 10 ^ 70 +
        3727834088785353505412994375575879413400146680041620420813934836878107) * 10 ^ 70 +
        9530835731746400678545619540041750243908483337504517139437848595532445) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 460,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (459 - x)) = _
  rw [show 460 = 273 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 24 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_459_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_459_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_460_prefix_zero :
    (∑ x ∈ Finset.range 274,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (460 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (460 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar2Left_coeff_460_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence4LeadingSquare.coeff (329 + x) *
        remainder4Coefficient2.coeff (460 - (329 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4LeadingSquare_coeff_high (329 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_460 :
    recurrence4Scalar2Left.coeff 460 =
      -((((77176331542928346 * 10 ^ 70 +
        1845022550509563754894219588692459401666768163588798819141349087803195) * 10 ^ 70 +
        3388096902413920839788455458946719360873454334829910838331142195814649) * 10 ^ 70 +
        3329691709835002211738849332038032685290773661357231744319978158676434) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 461,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (460 - x)) = _
  rw [show 461 = 274 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 23 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_460_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar2Left_coeff_460_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
