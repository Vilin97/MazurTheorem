/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart1Simp
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
  recurrence4A2_coeff_0
  recurrence4A2_coeff_1
  recurrence4A2_coeff_10
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
  recurrence4A2_coeff_11
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
  recurrence4A2_coeff_12
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
  recurrence4A2_coeff_13
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
  recurrence4A2_coeff_14
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
  recurrence4A2_coeff_15
  recurrence4A2_coeff_150
  recurrence4A2_coeff_151
  recurrence4A2_coeff_152
  recurrence4A2_coeff_153
  recurrence4A2_coeff_154
  recurrence4A2_coeff_155

attribute [local simp]
  recurrence4A2_coeff_156
  recurrence4A2_coeff_157
  recurrence4A2_coeff_158
  recurrence4A2_coeff_159
  recurrence4A2_coeff_16
  recurrence4A2_coeff_160
  recurrence4A2_coeff_161
  recurrence4A2_coeff_162
  recurrence4A2_coeff_163
  recurrence4A2_coeff_164
  recurrence4A2_coeff_165
  recurrence4A2_coeff_166
  recurrence4A2_coeff_167
  recurrence4A2_coeff_168
  recurrence4A2_coeff_169
  recurrence4A2_coeff_17
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
  recurrence4A2_coeff_18
  recurrence4A2_coeff_180
  recurrence4A2_coeff_181
  recurrence4A2_coeff_182
  recurrence4A2_coeff_183
  recurrence4A2_coeff_184
  recurrence4A2_coeff_185
  recurrence4A2_coeff_186
  recurrence4A2_coeff_19
  recurrence4A2_coeff_2
  recurrence4A2_coeff_20
  recurrence4A2_coeff_21
  recurrence4A2_coeff_22
  recurrence4A2_coeff_23
  recurrence4A2_coeff_24
  recurrence4A2_coeff_25
  recurrence4A2_coeff_26
  recurrence4A2_coeff_27
  recurrence4A2_coeff_28
  recurrence4A2_coeff_29
  recurrence4A2_coeff_3
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
  recurrence4A2_coeff_4
  recurrence4A2_coeff_40
  recurrence4A2_coeff_41
  recurrence4A2_coeff_42
  recurrence4A2_coeff_43
  recurrence4A2_coeff_44
  recurrence4A2_coeff_45

attribute [local simp]
  recurrence4A2_coeff_46
  recurrence4A2_coeff_47
  recurrence4A2_coeff_48
  recurrence4A2_coeff_49
  recurrence4A2_coeff_5
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
  recurrence4A2_coeff_6
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
  recurrence4A2_coeff_7
  recurrence4A2_coeff_70
  recurrence4A2_coeff_71
  recurrence4A2_coeff_72
  recurrence4A2_coeff_73
  recurrence4A2_coeff_74
  recurrence4A2_coeff_75
  recurrence4A2_coeff_76
  recurrence4A2_coeff_77
  recurrence4A2_coeff_78
  recurrence4A2_coeff_79
  recurrence4A2_coeff_8
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
  recurrence4A2_coeff_9
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
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101
  recurrence4LeadingSquare_coeff_102
  recurrence4LeadingSquare_coeff_103
  recurrence4LeadingSquare_coeff_104

attribute [local simp]
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
  recurrence4LeadingSquare_coeff_166
  recurrence4LeadingSquare_coeff_167
  recurrence4LeadingSquare_coeff_168

attribute [local simp]
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
  recurrence4LeadingSquare_coeff_230
  recurrence4LeadingSquare_coeff_231
  recurrence4LeadingSquare_coeff_232

attribute [local simp]
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
  recurrence4LeadingSquare_coeff_294
  recurrence4LeadingSquare_coeff_295
  recurrence4LeadingSquare_coeff_296

attribute [local simp]
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
  recurrence4LeadingSquare_coeff_38
  recurrence4LeadingSquare_coeff_39
  recurrence4LeadingSquare_coeff_40
  recurrence4LeadingSquare_coeff_41
  recurrence4LeadingSquare_coeff_42
  recurrence4LeadingSquare_coeff_43
  recurrence4LeadingSquare_coeff_44
  recurrence4LeadingSquare_coeff_45
  recurrence4LeadingSquare_coeff_46
  recurrence4LeadingSquare_coeff_47
  recurrence4LeadingSquare_coeff_48
  recurrence4LeadingSquare_coeff_49
  recurrence4LeadingSquare_coeff_50
  recurrence4LeadingSquare_coeff_51
  recurrence4LeadingSquare_coeff_52
  recurrence4LeadingSquare_coeff_53
  recurrence4LeadingSquare_coeff_54
  recurrence4LeadingSquare_coeff_55
  recurrence4LeadingSquare_coeff_56
  recurrence4LeadingSquare_coeff_57
  recurrence4LeadingSquare_coeff_58
  recurrence4LeadingSquare_coeff_59
  recurrence4LeadingSquare_coeff_60
  recurrence4LeadingSquare_coeff_61
  recurrence4LeadingSquare_coeff_62
  recurrence4LeadingSquare_coeff_63
  recurrence4LeadingSquare_coeff_64
  recurrence4LeadingSquare_coeff_65
  recurrence4LeadingSquare_coeff_66
  recurrence4LeadingSquare_coeff_67
  recurrence4LeadingSquare_coeff_68
  recurrence4LeadingSquare_coeff_69

attribute [local simp]
  recurrence4LeadingSquare_coeff_70
  recurrence4LeadingSquare_coeff_71
  recurrence4LeadingSquare_coeff_72
  recurrence4LeadingSquare_coeff_73
  recurrence4LeadingSquare_coeff_74
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

private theorem recurrence4Scalar2Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (259 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_259 :
    recurrence4Scalar2Left.coeff 259 =
      (((((745105425720720285176754944 * 10 ^ 70 +
        1042285951494587144220998301905695694348348425733516929256252085465076) * 10 ^ 70 +
        0204437735025303823263593747407708049412561147926472774670264724335808) * 10 ^ 70 +
        8753982213102303125995110382570271004404848361636127428289721370052489) * 10 ^ 70 +
        4098999361567330261467376069250538306054212220140310640475739190928295) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (259 - x)) = _
  rw [show 260 = 73 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_259_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (260 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_260 :
    recurrence4Scalar2Left.coeff 260 =
      -(((((815406996075062416622444584 * 10 ^ 70 +
        0659740112520904219161355399804719635635500373264683200387790010712641) * 10 ^ 70 +
        6283433070557479105397511075296883200453194358431239728987530757354061) * 10 ^ 70 +
        1889923722950531713752764780962456461459306290135986787727724742031896) * 10 ^ 70 +
        7264499618372504156647543169231936386089272549081441776564118222710905) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (260 - x)) = _
  rw [show 261 = 74 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_260_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (261 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_261 :
    recurrence4Scalar2Left.coeff 261 =
      (((((837663305172459654529748294 * 10 ^ 70 +
        0445156403594879554185600683522422643573876540369998312272623367379552) * 10 ^ 70 +
        5209650587592549267655411725807440140576360206298436218562704622906821) * 10 ^ 70 +
        2243262808659096910270224840316675313705470095834400497272648955063430) * 10 ^ 70 +
        5658729491507708377855433119406804389524227902780518430869693293998895) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (261 - x)) = _
  rw [show 262 = 75 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_261_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (262 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_262 :
    recurrence4Scalar2Left.coeff 262 =
      -(((((817877420232919413728264532 * 10 ^ 70 +
        9969429710333159656724885125991986724457827123834689682586943923930525) * 10 ^ 70 +
        3419859542443618447234342126566984987642718432592220972931009745343776) * 10 ^ 70 +
        4103697291943484980690060715491099989166126509416093283865528705056136) * 10 ^ 70 +
        6445828274918419670972378914029325802828966255792217919432767353807792) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (262 - x)) = _
  rw [show 263 = 76 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_262_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (263 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_263 :
    recurrence4Scalar2Left.coeff 263 =
      (((((763860856185412983286371006 * 10 ^ 70 +
        7471657330883190399789812200796883659675875948766838212906420291110090) * 10 ^ 70 +
        5687179094618332929087903434894672172999637290812222139609426870884804) * 10 ^ 70 +
        7041985837764637284455535620389966796762676288588284479658165411272160) * 10 ^ 70 +
        9300242519567959606948293963320261452772649249200137040961968183199752) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (263 - x)) = _
  rw [show 264 = 77 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_263_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (264 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_264 :
    recurrence4Scalar2Left.coeff 264 =
      -(((((684428188266827745715029805 * 10 ^ 70 +
        0007180712813478105877838293408993085004959717890631446019707281464928) * 10 ^ 70 +
        8415626357576365930674179374846274646793056306942881086212184114685524) * 10 ^ 70 +
        9564421884296758660178176402196494790161165541084677271074185389662149) * 10 ^ 70 +
        1000821123218295339431576498570536678014119738709681737409098573432705) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (264 - x)) = _
  rw [show 265 = 78 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_264_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (265 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_265 :
    recurrence4Scalar2Left.coeff 265 =
      (((((588604146434267094195278449 * 10 ^ 70 +
        5470722690375374217105549192040209100994605522331090090658181823338050) * 10 ^ 70 +
        7300513851014579561456663533110869253099271851098141253996617714560218) * 10 ^ 70 +
        6535280028090438417083900405571494867854214365797676714604605972636266) * 10 ^ 70 +
        7225511788085231813051509658002310931166201789389316183144518946034556) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (265 - x)) = _
  rw [show 266 = 79 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_265_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (266 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_266 :
    recurrence4Scalar2Left.coeff 266 =
      -(((((484919802426364505854535777 * 10 ^ 70 +
        5659235572965577003591662962190603534832298874935441475823114205186026) * 10 ^ 70 +
        4887830132364199623088957534908121387102933816341111672598817038231619) * 10 ^ 70 +
        0415668067031967601297892173949584491731908695677633830456038289395208) * 10 ^ 70 +
        4344051731006922581815520728296716472119618038990179503735748887889378) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (266 - x)) = _
  rw [show 267 = 80 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_266_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (267 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_267 :
    recurrence4Scalar2Left.coeff 267 =
      (((((380855060403807159728191676 * 10 ^ 70 +
        9084945672012643509151023180379920501059495725733701072249527324684052) * 10 ^ 70 +
        3374591963334432948336564781375822834442477736086035382359226259284864) * 10 ^ 70 +
        6228926172405666422342593751104770971980467868632430852312931173381601) * 10 ^ 70 +
        6765731808701473211794156557641210498382968470427759649281883369831429) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (267 - x)) = _
  rw [show 268 = 81 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_267_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (268 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_268 :
    recurrence4Scalar2Left.coeff 268 =
      -(((((282460719628668577513333725 * 10 ^ 70 +
        5077758695279105748241705794089829015498245577961339419994779900086829) * 10 ^ 70 +
        4359220462204603374558571838204165740544088353529113539714565271845846) * 10 ^ 70 +
        7273270949934562881447687456014358523535000166267396187915208134113601) * 10 ^ 70 +
        0368678765231558129525312860335061902241618489343297208250801965925485) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (268 - x)) = _
  rw [show 269 = 82 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_268_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (269 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_269 :
    recurrence4Scalar2Left.coeff 269 =
      (((((194168693384062568161112836 * 10 ^ 70 +
        8450091853270817393402994877152064034692452872009436231610340908994241) * 10 ^ 70 +
        2521394895165675815089264744685353510843420895034235788641893082982176) * 10 ^ 70 +
        9726863239306676701565626733665193190788447788232056315408847762746303) * 10 ^ 70 +
        5120699943173519370847161795684628237104848107215157112331350658022677) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (269 - x)) = _
  rw [show 270 = 83 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_269_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (270 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_270 :
    recurrence4Scalar2Left.coeff 270 =
      -(((((118776946138588391647861703 * 10 ^ 70 +
        1613563932469574295308131026991837660242524106813696973164494952309146) * 10 ^ 70 +
        2314622329018280170048449065254694378399669694315668501943584449482710) * 10 ^ 70 +
        8845275257804322077389946142758872715612451435569015891014576037677234) * 10 ^ 70 +
        3680593077249993203991074549511665740698248868163858409188513336122018) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (270 - x)) = _
  rw [show 271 = 84 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_270_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (271 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_271 :
    recurrence4Scalar2Left.coeff 271 =
      (((((57578876915072175515328543 * 10 ^ 70 +
        3852652407564879794402708688623270809120962808720938791398822298949288) * 10 ^ 70 +
        7326835204642171831426896060375486559807436550179614786592556693740821) * 10 ^ 70 +
        7740065317468197690191062742404132529858933552847144299065337461576511) * 10 ^ 70 +
        3102869140130965689196833307523060314912624278191943157021808754341026) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (271 - x)) = _
  rw [show 272 = 85 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_271_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (272 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_272 :
    recurrence4Scalar2Left.coeff 272 =
      -(((((10596613640910538938590846 * 10 ^ 70 +
        6696196897217580406984030249218294398388577214059059806466028940372782) * 10 ^ 70 +
        2912427553941814217499991255515238308225254409174857919476077321756027) * 10 ^ 70 +
        2799044984835467914770641474524351482371426197331445378482192098147243) * 10 ^ 70 +
        7303510515680795460481892429408328265812995185897430310385613697233305) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (272 - x)) = _
  rw [show 273 = 86 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_272_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (273 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_273 :
    recurrence4Scalar2Left.coeff 273 =
      -(((((23125803389655357949876720 * 10 ^ 70 +
        4738908338777047027077507613243633680406248949245878135213564099493154) * 10 ^ 70 +
        5915571096019516406257296593291624807321496899279125595341229681057697) * 10 ^ 70 +
        3642454211004799629993250634220559893818062391541315744816906865928215) * 10 ^ 70 +
        3720107693253918078047118911623153803266899495893446903821544543010838) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (273 - x)) = _
  rw [show 274 = 87 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_273_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (274 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_274 :
    recurrence4Scalar2Left.coeff 274 =
      (((((45210883936938392753701905 * 10 ^ 70 +
        2205510956782540426054457239031746517386280900920306955782118505323180) * 10 ^ 70 +
        1684035566579342761454190493714266141292430390139516178179091206105319) * 10 ^ 70 +
        8313283775024903125913369897060837479836169894773385173132675292863831) * 10 ^ 70 +
        3477038520033396823859379670751634997957678621224807453492678891808795) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (274 - x)) = _
  rw [show 275 = 88 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_274_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (275 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_275 :
    recurrence4Scalar2Left.coeff 275 =
      -(((((57652375597862623522217374 * 10 ^ 70 +
        9497727295556199919038448131945494389119213936231604431518250895105893) * 10 ^ 70 +
        6058184454688257810794650040510106421314072500174655865088640167082086) * 10 ^ 70 +
        3623787673765516624105772668624515132661642673052389270396694151730306) * 10 ^ 70 +
        6388265579014649902660999952094218603772563670097108102787930974159465) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (275 - x)) = _
  rw [show 276 = 89 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_275_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (276 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_276 :
    recurrence4Scalar2Left.coeff 276 =
      (((((62561172602217601732976356 * 10 ^ 70 +
        6876909675585656452532676633398620099202179443461578079719115242589892) * 10 ^ 70 +
        3038835895027648871798247474664456415293002166147636202346179644718639) * 10 ^ 70 +
        2466491610477239799270034101402895594240461198462995162133497204656739) * 10 ^ 70 +
        2611905257824030772726579584307376445514793742234048040666420078493165) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (276 - x)) = _
  rw [show 277 = 90 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_276_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (277 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_277 :
    recurrence4Scalar2Left.coeff 277 =
      -(((((61967054809696525318348391 * 10 ^ 70 +
        0847152700974621155085400020208884748369506054520229360004219353080482) * 10 ^ 70 +
        4061979626177829980153013173953104807082584818363942363437343968784641) * 10 ^ 70 +
        6904996392604606353111064517224169354440239126435571425397516900430986) * 10 ^ 70 +
        7158538384528211674128226272863265052163410973991109628340025819497681) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 278,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (277 - x)) = _
  rw [show 278 = 91 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_277_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (278 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_278 :
    recurrence4Scalar2Left.coeff 278 =
      (((((57681212342988105233159483 * 10 ^ 70 +
        4615706214489629259702901912129387375812970520397901283081215395297242) * 10 ^ 70 +
        9335247178685789153568417893311655429330126375231184017434230945734869) * 10 ^ 70 +
        8952540631124723264155342499079945811246959700459714453367050542627041) * 10 ^ 70 +
        1619618812945616849172420605867133726047516594149223236320510860437578) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 279,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (278 - x)) = _
  rw [show 279 = 92 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_278_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (279 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_279 :
    recurrence4Scalar2Left.coeff 279 =
      -(((((51216666802728196560820766 * 10 ^ 70 +
        0450229871572831244370173047030169699643317113079528572758920751905164) * 10 ^ 70 +
        9015076049260109086454877156613192380533889255676673685577715491008315) * 10 ^ 70 +
        3877779069313311169383023978665265890603112303834716764409556346265620) * 10 ^ 70 +
        0386233569146113995276055174933188796188882482543281528843760473574452) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 280,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (279 - x)) = _
  rw [show 280 = 93 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_279_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (280 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_280 :
    recurrence4Scalar2Left.coeff 280 =
      (((((43758226914032361474920643 * 10 ^ 70 +
        3199207919737012884716080178182906841229032751476412449496642931328656) * 10 ^ 70 +
        3705597219679087814191717650869128923785229628980653658268461981363211) * 10 ^ 70 +
        0618784452331847993841125051889529688292546526632760739426888946936087) * 10 ^ 70 +
        4497089492543136751722838456736848477411887989753065085247807036048651) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 281,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (280 - x)) = _
  rw [show 281 = 94 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_280_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (281 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_281 :
    recurrence4Scalar2Left.coeff 281 =
      -(((((36170603433059040155967069 * 10 ^ 70 +
        1270469301155999919649615193990280517812847237827579709243970339830326) * 10 ^ 70 +
        2089679548538105700423718081569793103228047004945711069474125605592748) * 10 ^ 70 +
        4460773490856863244081545990667220411451780502713938559902951046051503) * 10 ^ 70 +
        2266431802364242478366016996163196616173799058016878895279195077358810) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 282,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (281 - x)) = _
  rw [show 282 = 95 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_281_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (282 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_282 :
    recurrence4Scalar2Left.coeff 282 =
      (((((29032477681655414858353121 * 10 ^ 70 +
        8966367783368371315516232773304545036403417159791086463880127649003350) * 10 ^ 70 +
        1581594967058051457519277370035016223949530933299766077515196150286980) * 10 ^ 70 +
        3771231487708719668781454225517786398346353666927324564800370253340916) * 10 ^ 70 +
        3657493771268228704384781924199654027459529076556503858371064287296312) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 283,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (282 - x)) = _
  rw [show 283 = 96 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_282_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (283 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_283 :
    recurrence4Scalar2Left.coeff 283 =
      -(((((22685164982675840344968713 * 10 ^ 70 +
        7766063035355633494318408104016514403997334225899640250870019903875353) * 10 ^ 70 +
        4370402915054742365921380914375357940799865818288082438387261544906017) * 10 ^ 70 +
        3642640559847283144282756099209818967314786606504032355286142082658849) * 10 ^ 70 +
        2080555318986756401540967107169539537471222616967271576797805410395781) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 284,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (283 - x)) = _
  rw [show 284 = 97 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_283_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (284 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_284 :
    recurrence4Scalar2Left.coeff 284 =
      (((((17286443590494531228099684 * 10 ^ 70 +
        7691899000045201366981274190112366967214769293032177767821017314546204) * 10 ^ 70 +
        4941901417219064137411959077035925104745265038422202936847306291215020) * 10 ^ 70 +
        2817614365774668179196071637046030248879149022950639493273152389177870) * 10 ^ 70 +
        9743647434460274963995200599965296975155154072813588643123010323325845) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 285,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (284 - x)) = _
  rw [show 285 = 98 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_284_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (285 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_285 :
    recurrence4Scalar2Left.coeff 285 =
      -(((((12862560754128589287683682 * 10 ^ 70 +
        9481573571875942619947761665134624217798715278137432431959653805738326) * 10 ^ 70 +
        3448074152476267578699724867744272291964321175535280559898745185431378) * 10 ^ 70 +
        8732273920859819287500210758174588145404204499237301779775853857717658) * 10 ^ 70 +
        7824975210920765365987784997565677756910341821692158655033978495773637) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 286,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (285 - x)) = _
  rw [show 286 = 99 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_285_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (286 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_286 :
    recurrence4Scalar2Left.coeff 286 =
      (((((9353911301154453926786167 * 10 ^ 70 +
        2610399137814125838027166355392172272576954930669416217910011982286733) * 10 ^ 70 +
        9860281999391654947493896940438660721091204548701246004463989957669082) * 10 ^ 70 +
        2517995044712549290635610670307847453870564907787269169988260899162598) * 10 ^ 70 +
        4946037995979948271718050038854792614422502550602005402487352274239101) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 287,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (286 - x)) = _
  rw [show 287 = 100 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_286_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (287 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_287 :
    recurrence4Scalar2Left.coeff 287 =
      -(((((6652081632201668586155066 * 10 ^ 70 +
        9272745163868286375702470704591797028502410516221241044213934812023000) * 10 ^ 70 +
        1792991335059353795605872183860166137793674776480533182242677294255785) * 10 ^ 70 +
        9861224603996412325790870185646760178788214895063793920780945557372906) * 10 ^ 70 +
        9070866227728621625548102384118993715111890761216422839784508683777876) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 288,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (287 - x)) = _
  rw [show 288 = 101 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_287_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (288 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_288 :
    recurrence4Scalar2Left.coeff 288 =
      (((((4627678912466691551614650 * 10 ^ 70 +
        9451273827582153507977622592993822812929007634214190151737173153941605) * 10 ^ 70 +
        9587725531271427939413154145246285664546357188520614792495457345543022) * 10 ^ 70 +
        9437348331119747547000658962197467000514218251696276557318660976307711) * 10 ^ 70 +
        2334816417035988440327847111560628472419351272931461553382809215509640) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 289,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (288 - x)) = _
  rw [show 289 = 102 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_288_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (289 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_289 :
    recurrence4Scalar2Left.coeff 289 =
      -(((((3149562183150964047365745 * 10 ^ 70 +
        7559551859646986601579344556403637957957382102033717008735846273367903) * 10 ^ 70 +
        5354227566694279186630714317103411141310187523717538488027977305785001) * 10 ^ 70 +
        2843621641774375677698031525905508653922100920792859295105069785742642) * 10 ^ 70 +
        5523249091985727284713729449188180224949041254506863442331487738991835) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 290,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (289 - x)) = _
  rw [show 290 = 103 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_289_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (290 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_290 :
    recurrence4Scalar2Left.coeff 290 =
      (((((2096791942489283004463699 * 10 ^ 70 +
        0325516038312708031438601707145585600335124118623300915663433336151614) * 10 ^ 70 +
        6003414768569847104913287855776935371886171217291904822369838904516931) * 10 ^ 70 +
        1287436787900103442884040709228357519849581179944874478350901342827539) * 10 ^ 70 +
        2904358553599015461845113912456274094401822939349135098941211679462493) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 291,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (290 - x)) = _
  rw [show 291 = 104 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_290_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (291 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_291 :
    recurrence4Scalar2Left.coeff 291 =
      -(((((1364906301720155408930823 * 10 ^ 70 +
        6131850846697172423659543111749319123324838457146576303314534574453182) * 10 ^ 70 +
        7924655666730675876711251986175964586426858295486857480753944815462815) * 10 ^ 70 +
        9477335259101705542977495198005440357640698531406095804761701830856831) * 10 ^ 70 +
        2410610329846305958518073349652827951221616458168471397959260650767506) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 292,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (291 - x)) = _
  rw [show 292 = 105 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_291_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (292 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_292 :
    recurrence4Scalar2Left.coeff 292 =
      (((((868127442104021087146706 * 10 ^ 70 +
        2433454664636871404597800396362113045466840631349354503144863706138859) * 10 ^ 70 +
        5443910638343289448398708337456810223369372941254595566526225632450233) * 10 ^ 70 +
        7483125263949639427285343804568468748633369356682566897859514239347637) * 10 ^ 70 +
        5200679545379955716879936411022474454571711515487992088727150273978375) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 293,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (292 - x)) = _
  rw [show 293 = 106 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_292_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar2Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (293 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_293 :
    recurrence4Scalar2Left.coeff 293 =
      -(((((538912927804086539361346 * 10 ^ 70 +
        6539535799061109648735063054911737561066571409890397238833948811691277) * 10 ^ 70 +
        1764926668853021256672635721124721665877374903855850897214758853090013) * 10 ^ 70 +
        9070273052686567589136762446611774593633323480327662595022434083121820) * 10 ^ 70 +
        3094845294976120781607063350574162102156273192910368327079859619719421) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 294,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (293 - x)) = _
  rw [show 294 = 107 +
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar2Left_coeff_293_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
