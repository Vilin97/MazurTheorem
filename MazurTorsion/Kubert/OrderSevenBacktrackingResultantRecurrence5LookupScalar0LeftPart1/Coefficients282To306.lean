/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5LeadingSquare_coeff_0
  recurrence5LeadingSquare_coeff_1
  recurrence5LeadingSquare_coeff_2
  recurrence5LeadingSquare_coeff_3
  recurrence5LeadingSquare_coeff_4
  recurrence5LeadingSquare_coeff_5
  recurrence5LeadingSquare_coeff_6
  recurrence5LeadingSquare_coeff_7
  recurrence5LeadingSquare_coeff_8
  recurrence5LeadingSquare_coeff_9
  recurrence5LeadingSquare_coeff_10
  recurrence5LeadingSquare_coeff_11
  recurrence5LeadingSquare_coeff_12
  recurrence5LeadingSquare_coeff_13
  recurrence5LeadingSquare_coeff_14
  recurrence5LeadingSquare_coeff_15
  recurrence5LeadingSquare_coeff_16
  recurrence5LeadingSquare_coeff_17
  recurrence5LeadingSquare_coeff_18
  recurrence5LeadingSquare_coeff_19
  recurrence5LeadingSquare_coeff_20
  recurrence5LeadingSquare_coeff_21
  recurrence5LeadingSquare_coeff_22
  recurrence5LeadingSquare_coeff_23
  recurrence5LeadingSquare_coeff_24
  recurrence5LeadingSquare_coeff_25
  recurrence5LeadingSquare_coeff_26
  recurrence5LeadingSquare_coeff_27
  recurrence5LeadingSquare_coeff_28
  recurrence5LeadingSquare_coeff_29
  recurrence5LeadingSquare_coeff_30
  recurrence5LeadingSquare_coeff_31
  recurrence5LeadingSquare_coeff_32
  recurrence5LeadingSquare_coeff_33
  recurrence5LeadingSquare_coeff_34
  recurrence5LeadingSquare_coeff_35
  recurrence5LeadingSquare_coeff_36
  recurrence5LeadingSquare_coeff_37
  recurrence5LeadingSquare_coeff_38
  recurrence5LeadingSquare_coeff_39
  recurrence5LeadingSquare_coeff_40
  recurrence5LeadingSquare_coeff_41
  recurrence5LeadingSquare_coeff_42
  recurrence5LeadingSquare_coeff_43
  recurrence5LeadingSquare_coeff_44
  recurrence5LeadingSquare_coeff_45
  recurrence5LeadingSquare_coeff_46
  recurrence5LeadingSquare_coeff_47
  recurrence5LeadingSquare_coeff_48
  recurrence5LeadingSquare_coeff_49
  recurrence5LeadingSquare_coeff_50
  recurrence5LeadingSquare_coeff_51
  recurrence5LeadingSquare_coeff_52
  recurrence5LeadingSquare_coeff_53
  recurrence5LeadingSquare_coeff_54
  recurrence5LeadingSquare_coeff_55
  recurrence5LeadingSquare_coeff_56
  recurrence5LeadingSquare_coeff_57
  recurrence5LeadingSquare_coeff_58
  recurrence5LeadingSquare_coeff_59
  recurrence5LeadingSquare_coeff_60
  recurrence5LeadingSquare_coeff_61
  recurrence5LeadingSquare_coeff_62
  recurrence5LeadingSquare_coeff_63

attribute [local simp]
  recurrence5LeadingSquare_coeff_64
  recurrence5LeadingSquare_coeff_65
  recurrence5LeadingSquare_coeff_66
  recurrence5LeadingSquare_coeff_67
  recurrence5LeadingSquare_coeff_68
  recurrence5LeadingSquare_coeff_69
  recurrence5LeadingSquare_coeff_70
  recurrence5LeadingSquare_coeff_71
  recurrence5LeadingSquare_coeff_72
  recurrence5LeadingSquare_coeff_73
  recurrence5LeadingSquare_coeff_74
  recurrence5LeadingSquare_coeff_75
  recurrence5LeadingSquare_coeff_76
  recurrence5LeadingSquare_coeff_77
  recurrence5LeadingSquare_coeff_78
  recurrence5LeadingSquare_coeff_79
  recurrence5LeadingSquare_coeff_80
  recurrence5LeadingSquare_coeff_81
  recurrence5LeadingSquare_coeff_82
  recurrence5LeadingSquare_coeff_83
  recurrence5LeadingSquare_coeff_84
  recurrence5LeadingSquare_coeff_85
  recurrence5LeadingSquare_coeff_86
  recurrence5LeadingSquare_coeff_87
  recurrence5LeadingSquare_coeff_88
  recurrence5LeadingSquare_coeff_89
  recurrence5LeadingSquare_coeff_90
  recurrence5LeadingSquare_coeff_91
  recurrence5LeadingSquare_coeff_92
  recurrence5LeadingSquare_coeff_93
  recurrence5LeadingSquare_coeff_94
  recurrence5LeadingSquare_coeff_95
  recurrence5LeadingSquare_coeff_96
  recurrence5LeadingSquare_coeff_97
  recurrence5LeadingSquare_coeff_98
  recurrence5LeadingSquare_coeff_99
  recurrence5LeadingSquare_coeff_100
  recurrence5LeadingSquare_coeff_101
  recurrence5LeadingSquare_coeff_102
  recurrence5LeadingSquare_coeff_103
  recurrence5LeadingSquare_coeff_104
  recurrence5LeadingSquare_coeff_105
  recurrence5LeadingSquare_coeff_106
  recurrence5LeadingSquare_coeff_107
  recurrence5LeadingSquare_coeff_108
  recurrence5LeadingSquare_coeff_109
  recurrence5LeadingSquare_coeff_110
  recurrence5LeadingSquare_coeff_111
  recurrence5LeadingSquare_coeff_112
  recurrence5LeadingSquare_coeff_113
  recurrence5LeadingSquare_coeff_114
  recurrence5LeadingSquare_coeff_115
  recurrence5LeadingSquare_coeff_116
  recurrence5LeadingSquare_coeff_117
  recurrence5LeadingSquare_coeff_118
  recurrence5LeadingSquare_coeff_119
  recurrence5LeadingSquare_coeff_120
  recurrence5LeadingSquare_coeff_121
  recurrence5LeadingSquare_coeff_122
  recurrence5LeadingSquare_coeff_123
  recurrence5LeadingSquare_coeff_124
  recurrence5LeadingSquare_coeff_125
  recurrence5LeadingSquare_coeff_126
  recurrence5LeadingSquare_coeff_127

attribute [local simp]
  recurrence5LeadingSquare_coeff_128
  recurrence5LeadingSquare_coeff_129
  recurrence5LeadingSquare_coeff_130
  recurrence5LeadingSquare_coeff_131
  recurrence5LeadingSquare_coeff_132
  recurrence5LeadingSquare_coeff_133
  recurrence5LeadingSquare_coeff_134
  recurrence5LeadingSquare_coeff_135
  recurrence5LeadingSquare_coeff_136
  recurrence5LeadingSquare_coeff_137
  recurrence5LeadingSquare_coeff_138
  recurrence5LeadingSquare_coeff_139
  recurrence5LeadingSquare_coeff_140
  recurrence5LeadingSquare_coeff_141
  recurrence5LeadingSquare_coeff_142
  recurrence5LeadingSquare_coeff_143
  recurrence5LeadingSquare_coeff_144
  recurrence5LeadingSquare_coeff_145
  recurrence5LeadingSquare_coeff_146
  recurrence5LeadingSquare_coeff_147
  recurrence5LeadingSquare_coeff_148
  recurrence5LeadingSquare_coeff_149
  recurrence5LeadingSquare_coeff_150
  recurrence5LeadingSquare_coeff_151
  recurrence5LeadingSquare_coeff_152
  recurrence5LeadingSquare_coeff_153
  recurrence5LeadingSquare_coeff_154
  recurrence5LeadingSquare_coeff_155
  recurrence5LeadingSquare_coeff_156
  recurrence5LeadingSquare_coeff_157
  recurrence5LeadingSquare_coeff_158
  recurrence5LeadingSquare_coeff_159
  recurrence5LeadingSquare_coeff_160
  recurrence5LeadingSquare_coeff_161
  recurrence5LeadingSquare_coeff_162
  recurrence5LeadingSquare_coeff_163
  recurrence5LeadingSquare_coeff_164
  recurrence5LeadingSquare_coeff_165
  recurrence5LeadingSquare_coeff_166
  recurrence5LeadingSquare_coeff_167
  recurrence5LeadingSquare_coeff_168
  recurrence5LeadingSquare_coeff_169
  recurrence5LeadingSquare_coeff_170
  recurrence5LeadingSquare_coeff_171
  recurrence5LeadingSquare_coeff_172
  recurrence5LeadingSquare_coeff_173
  recurrence5LeadingSquare_coeff_174
  recurrence5LeadingSquare_coeff_175
  recurrence5LeadingSquare_coeff_176
  recurrence5LeadingSquare_coeff_177
  recurrence5LeadingSquare_coeff_178
  recurrence5LeadingSquare_coeff_179
  recurrence5LeadingSquare_coeff_180
  recurrence5LeadingSquare_coeff_181
  recurrence5LeadingSquare_coeff_182
  recurrence5LeadingSquare_coeff_183
  recurrence5LeadingSquare_coeff_184
  recurrence5LeadingSquare_coeff_185
  recurrence5LeadingSquare_coeff_186
  recurrence5LeadingSquare_coeff_187
  recurrence5LeadingSquare_coeff_188
  recurrence5LeadingSquare_coeff_189
  recurrence5LeadingSquare_coeff_190
  recurrence5LeadingSquare_coeff_191

attribute [local simp]
  recurrence5LeadingSquare_coeff_192
  recurrence5LeadingSquare_coeff_193
  recurrence5LeadingSquare_coeff_194
  recurrence5LeadingSquare_coeff_195
  recurrence5LeadingSquare_coeff_196
  recurrence5LeadingSquare_coeff_197
  recurrence5LeadingSquare_coeff_198
  recurrence5LeadingSquare_coeff_199
  recurrence5LeadingSquare_coeff_200
  recurrence5LeadingSquare_coeff_201
  recurrence5LeadingSquare_coeff_202
  recurrence5LeadingSquare_coeff_203
  recurrence5LeadingSquare_coeff_204
  recurrence5LeadingSquare_coeff_205
  recurrence5LeadingSquare_coeff_206
  recurrence5LeadingSquare_coeff_207
  recurrence5LeadingSquare_coeff_208
  recurrence5LeadingSquare_coeff_209
  recurrence5LeadingSquare_coeff_210
  recurrence5LeadingSquare_coeff_211
  recurrence5LeadingSquare_coeff_212
  recurrence5LeadingSquare_coeff_213
  recurrence5LeadingSquare_coeff_214
  recurrence5LeadingSquare_coeff_215
  recurrence5LeadingSquare_coeff_216
  recurrence5LeadingSquare_coeff_217
  recurrence5LeadingSquare_coeff_218
  recurrence5LeadingSquare_coeff_219
  recurrence5LeadingSquare_coeff_220
  recurrence5LeadingSquare_coeff_221
  recurrence5LeadingSquare_coeff_222
  recurrence5LeadingSquare_coeff_223
  recurrence5LeadingSquare_coeff_224
  recurrence5LeadingSquare_coeff_225
  recurrence5LeadingSquare_coeff_226
  recurrence5LeadingSquare_coeff_227
  recurrence5LeadingSquare_coeff_228
  recurrence5LeadingSquare_coeff_229
  recurrence5LeadingSquare_coeff_230
  recurrence5LeadingSquare_coeff_231
  recurrence5LeadingSquare_coeff_232
  recurrence5LeadingSquare_coeff_233
  recurrence5LeadingSquare_coeff_234
  recurrence5LeadingSquare_coeff_235
  recurrence5LeadingSquare_coeff_236
  recurrence5LeadingSquare_coeff_237
  recurrence5LeadingSquare_coeff_238
  recurrence5LeadingSquare_coeff_239
  recurrence5LeadingSquare_coeff_240
  recurrence5LeadingSquare_coeff_241
  recurrence5LeadingSquare_coeff_242
  recurrence5LeadingSquare_coeff_243
  recurrence5LeadingSquare_coeff_244
  recurrence5LeadingSquare_coeff_245
  recurrence5LeadingSquare_coeff_246
  recurrence5LeadingSquare_coeff_247
  recurrence5LeadingSquare_coeff_248
  recurrence5LeadingSquare_coeff_249
  recurrence5LeadingSquare_coeff_250
  recurrence5LeadingSquare_coeff_251
  recurrence5LeadingSquare_coeff_252
  recurrence5LeadingSquare_coeff_253
  recurrence5LeadingSquare_coeff_254
  recurrence5LeadingSquare_coeff_255

attribute [local simp]
  recurrence5LeadingSquare_coeff_256
  recurrence5LeadingSquare_coeff_257
  recurrence5LeadingSquare_coeff_258
  recurrence5LeadingSquare_coeff_259
  recurrence5LeadingSquare_coeff_260
  recurrence5LeadingSquare_coeff_261
  recurrence5LeadingSquare_coeff_262
  recurrence5LeadingSquare_coeff_263
  recurrence5LeadingSquare_coeff_264
  recurrence5LeadingSquare_coeff_265
  recurrence5LeadingSquare_coeff_266
  recurrence5LeadingSquare_coeff_267
  recurrence5LeadingSquare_coeff_268
  recurrence5LeadingSquare_coeff_269
  recurrence5LeadingSquare_coeff_270
  recurrence5LeadingSquare_coeff_271
  recurrence5LeadingSquare_coeff_272
  recurrence5LeadingSquare_coeff_273
  recurrence5LeadingSquare_coeff_274
  recurrence5LeadingSquare_coeff_275
  recurrence5LeadingSquare_coeff_276
  recurrence5LeadingSquare_coeff_277
  recurrence5LeadingSquare_coeff_278
  recurrence5LeadingSquare_coeff_279
  recurrence5LeadingSquare_coeff_280
  recurrence5LeadingSquare_coeff_281
  recurrence5LeadingSquare_coeff_282
  recurrence5LeadingSquare_coeff_283
  recurrence5LeadingSquare_coeff_284
  recurrence5LeadingSquare_coeff_285
  recurrence5LeadingSquare_coeff_286
  recurrence5LeadingSquare_coeff_287
  recurrence5LeadingSquare_coeff_288
  recurrence5LeadingSquare_coeff_289
  recurrence5LeadingSquare_coeff_290
  recurrence5A0_coeff_0
  recurrence5A0_coeff_1
  recurrence5A0_coeff_2
  recurrence5A0_coeff_3
  recurrence5A0_coeff_4
  recurrence5A0_coeff_5
  recurrence5A0_coeff_6
  recurrence5A0_coeff_7
  recurrence5A0_coeff_8
  recurrence5A0_coeff_9
  recurrence5A0_coeff_10
  recurrence5A0_coeff_11
  recurrence5A0_coeff_12
  recurrence5A0_coeff_13
  recurrence5A0_coeff_14
  recurrence5A0_coeff_15
  recurrence5A0_coeff_16
  recurrence5A0_coeff_17
  recurrence5A0_coeff_18
  recurrence5A0_coeff_19
  recurrence5A0_coeff_20
  recurrence5A0_coeff_21
  recurrence5A0_coeff_22
  recurrence5A0_coeff_23
  recurrence5A0_coeff_24
  recurrence5A0_coeff_25
  recurrence5A0_coeff_26
  recurrence5A0_coeff_27
  recurrence5A0_coeff_28

attribute [local simp]
  recurrence5A0_coeff_29
  recurrence5A0_coeff_30
  recurrence5A0_coeff_31
  recurrence5A0_coeff_32
  recurrence5A0_coeff_33
  recurrence5A0_coeff_34
  recurrence5A0_coeff_35
  recurrence5A0_coeff_36
  recurrence5A0_coeff_37
  recurrence5A0_coeff_38
  recurrence5A0_coeff_39
  recurrence5A0_coeff_40
  recurrence5A0_coeff_41
  recurrence5A0_coeff_42
  recurrence5A0_coeff_43
  recurrence5A0_coeff_44
  recurrence5A0_coeff_45
  recurrence5A0_coeff_46
  recurrence5A0_coeff_47
  recurrence5A0_coeff_48
  recurrence5A0_coeff_49
  recurrence5A0_coeff_50
  recurrence5A0_coeff_51
  recurrence5A0_coeff_52
  recurrence5A0_coeff_53
  recurrence5A0_coeff_54
  recurrence5A0_coeff_55
  recurrence5A0_coeff_56
  recurrence5A0_coeff_57
  recurrence5A0_coeff_58
  recurrence5A0_coeff_59
  recurrence5A0_coeff_60
  recurrence5A0_coeff_61
  recurrence5A0_coeff_62
  recurrence5A0_coeff_63
  recurrence5A0_coeff_64
  recurrence5A0_coeff_65
  recurrence5A0_coeff_66
  recurrence5A0_coeff_67
  recurrence5A0_coeff_68
  recurrence5A0_coeff_69
  recurrence5A0_coeff_70
  recurrence5A0_coeff_71
  recurrence5A0_coeff_72
  recurrence5A0_coeff_73
  recurrence5A0_coeff_74
  recurrence5A0_coeff_75
  recurrence5A0_coeff_76
  recurrence5A0_coeff_77
  recurrence5A0_coeff_78
  recurrence5A0_coeff_79
  recurrence5A0_coeff_80
  recurrence5A0_coeff_81
  recurrence5A0_coeff_82
  recurrence5A0_coeff_83
  recurrence5A0_coeff_84
  recurrence5A0_coeff_85
  recurrence5A0_coeff_86
  recurrence5A0_coeff_87
  recurrence5A0_coeff_88
  recurrence5A0_coeff_89
  recurrence5A0_coeff_90
  recurrence5A0_coeff_91
  recurrence5A0_coeff_92

attribute [local simp]
  recurrence5A0_coeff_93
  recurrence5A0_coeff_94
  recurrence5A0_coeff_95
  recurrence5A0_coeff_96
  recurrence5A0_coeff_97
  recurrence5A0_coeff_98
  recurrence5A0_coeff_99
  recurrence5A0_coeff_100
  recurrence5A0_coeff_101
  recurrence5A0_coeff_102
  recurrence5A0_coeff_103
  recurrence5A0_coeff_104
  recurrence5A0_coeff_105
  recurrence5A0_coeff_106
  recurrence5A0_coeff_107
  recurrence5A0_coeff_108
  recurrence5A0_coeff_109
  recurrence5A0_coeff_110
  recurrence5A0_coeff_111
  recurrence5A0_coeff_112
  recurrence5A0_coeff_113
  recurrence5A0_coeff_114
  recurrence5A0_coeff_115
  recurrence5A0_coeff_116
  recurrence5A0_coeff_117
  recurrence5A0_coeff_118
  recurrence5A0_coeff_119
  recurrence5A0_coeff_120
  recurrence5A0_coeff_121
  recurrence5A0_coeff_122
  recurrence5A0_coeff_123
  recurrence5A0_coeff_124
  recurrence5A0_coeff_125
  recurrence5A0_coeff_126
  recurrence5A0_coeff_127
  recurrence5A0_coeff_128
  recurrence5A0_coeff_129
  recurrence5A0_coeff_130
  recurrence5A0_coeff_131
  recurrence5A0_coeff_132
  recurrence5A0_coeff_133
  recurrence5A0_coeff_134
  recurrence5A0_coeff_135
  recurrence5A0_coeff_136
  recurrence5A0_coeff_137
  recurrence5A0_coeff_138
  recurrence5A0_coeff_139
  recurrence5A0_coeff_140
  recurrence5A0_coeff_141
  recurrence5A0_coeff_142
  recurrence5A0_coeff_143
  recurrence5A0_coeff_144
  recurrence5A0_coeff_145
  recurrence5A0_coeff_146
  recurrence5A0_coeff_147
  recurrence5A0_coeff_148
  recurrence5A0_coeff_149
  recurrence5A0_coeff_150
  recurrence5A0_coeff_151
  recurrence5A0_coeff_152
  recurrence5A0_coeff_153
  recurrence5A0_coeff_154
  recurrence5A0_coeff_155
  recurrence5A0_coeff_156

attribute [local simp]
  recurrence5A0_coeff_157
  recurrence5A0_coeff_158
  recurrence5A0_coeff_159
  recurrence5A0_coeff_160
  recurrence5A0_coeff_161
  recurrence5A0_coeff_162
  recurrence5A0_coeff_163
  recurrence5A0_coeff_164
  recurrence5A0_coeff_165
  recurrence5A0_coeff_166
  recurrence5A0_coeff_167
  recurrence5A0_coeff_168
  recurrence5A0_coeff_169
  recurrence5A0_coeff_170
  recurrence5A0_coeff_171
  recurrence5A0_coeff_172
  recurrence5A0_coeff_173
  recurrence5A0_coeff_174
  recurrence5A0_coeff_175
  recurrence5A0_coeff_176

private theorem recurrence5Scalar0Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_282 :
    recurrence5Scalar0Left.coeff 282 =
      -(((((1892157534458732982475818973931960779516488923591476816118673928530939 * 10 ^ 70 +
        6980848982681867776162421408192051415556122628058210005708178401090208) * 10 ^ 70 +
        6802182170638635849186996879510716975057631366808424704281612555507574) * 10 ^ 70 +
        9746450024828373767049279510197387214715801922958543661847489247495689) * 10 ^ 70 +
        7191143817123252842069615083399568352736461189948608521313907725937362) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 283 = 106 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_282_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_283 :
    recurrence5Scalar0Left.coeff 283 =
      (((((817931248770373204683822588869244943221751524107711202659955563260482 * 10 ^ 70 +
        3840547491188289559302999413945974484655537005235043496641613959019313) * 10 ^ 70 +
        0956760427344299886098241940830730595711960120446504944105173358105408) * 10 ^ 70 +
        8122670526651949016072680198809332398905043318493440797184012067566064) * 10 ^ 70 +
        1028078160053472784047925076682556864092530083444622989142619796647232) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 284 = 107 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_283_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_284 :
    recurrence5Scalar0Left.coeff 284 =
      -(((((325471689944215270414781256028833856992032969011623530998836850495279 * 10 ^ 70 +
        0749441264247665035259151904670647839532759493287992374900158511661020) * 10 ^ 70 +
        6487735413304923154229582828359243284166059824499877257692195215512711) * 10 ^ 70 +
        1621611925210601093180243147452777466991614855743233828768862349157965) * 10 ^ 70 +
        6767635995967415785786027436213687647472212034147516244982647671281610) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 285 = 108 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_284_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_285 :
    recurrence5Scalar0Left.coeff 285 =
      (((((118278745403984360486228899365400275505316815631332497096621383195945 * 10 ^ 70 +
        7860312064093565007780328605653396219381472012668482892106609170046245) * 10 ^ 70 +
        1528210574468730758650023109456937962023718408456798637663096315396555) * 10 ^ 70 +
        2970114321685595865941457298242052142475650239809883856529911374460811) * 10 ^ 70 +
        9090048303718968506423985640634872932468489463451526038354050040783841) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 286 = 109 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_285_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_286 :
    recurrence5Scalar0Left.coeff 286 =
      -(((((40180930082638558824893655110298042434288974950789659292346398441325 * 10 ^ 70 +
        3276016360875365411554831658593143456436617043207432257248843620902737) * 10 ^ 70 +
        5747496410312780156531819867800755342745201920901140199381766180971778) * 10 ^ 70 +
        8432351049443697829091580632513840366565949676331070690610061543632704) * 10 ^ 70 +
        2836539918412354963153798005842630209353540122395521969368904483679007) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 287 = 110 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_286_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_287 :
    recurrence5Scalar0Left.coeff 287 =
      (((((14860251006301894478299829471357721267443872896173680005978521219505 * 10 ^ 70 +
        6302055463378261608604932002275709776481152146807270647726505032393697) * 10 ^ 70 +
        9965997825829432939428614149003865532408221570691014256513856864355682) * 10 ^ 70 +
        7839083915250967973054342869703019976022426798747662398401475731020607) * 10 ^ 70 +
        4531007689231703462063013690986675596765451098027450786699405007872229) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 288 = 111 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_287_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_288 :
    recurrence5Scalar0Left.coeff 288 =
      -(((((8215046485848266910864321825101427430497922361712501644367810125240 * 10 ^ 70 +
        3997414350347271651388793700743686803704682308013897259895155405810202) * 10 ^ 70 +
        1294089284942141304788875174102461889934867618232392076084855789436247) * 10 ^ 70 +
        6288509404204246811024868167400063443086123462369143055586310593543298) * 10 ^ 70 +
        2356000080362291515236113318182961245470025518721170084730663213502425) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 289 = 112 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_288_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_289 :
    recurrence5Scalar0Left.coeff 289 =
      (((((6717636352184986250772835701380504753702882237041596141778937321169 * 10 ^ 70 +
        8399658710949507877203966248674748050196577048714007604020881878229946) * 10 ^ 70 +
        0444650313742820118223730501747243071910945505514632178087420944717520) * 10 ^ 70 +
        9573431120926361028518068515872401776036128028666983203802764464364087) * 10 ^ 70 +
        1219416641061909040897310728968522322003636928304076782578834995526676) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 290 = 113 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_289_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_290 :
    recurrence5Scalar0Left.coeff 290 =
      -(((((5921112849299857353101881392760384788825246322803152254439455127959 * 10 ^ 70 +
        1752679122205593913118913688288350150945558600895796469852031176255229) * 10 ^ 70 +
        6598118928472724740968495138920232005118355465868078442045155384427962) * 10 ^ 70 +
        8350213703622298765365759210645385973456130344045429920207779680314942) * 10 ^ 70 +
        6045949415425534326766822670352577572527840145780326578605297475688563) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 291 = 114 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_290_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (291 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_291 :
    recurrence5Scalar0Left.coeff 291 =
      (((((4869757762093114527334366764552989616874206470070043222542923116480 * 10 ^ 70 +
        2217075305716280791701528928034026858918503467162434731854185920468735) * 10 ^ 70 +
        5624321447323528032375987076021792464691180115534207451630622180823110) * 10 ^ 70 +
        8951413920628387118603111061173719536713296441091230059003307486905935) * 10 ^ 70 +
        0886632793238131261409615423080526703328187743578393296035542165112806) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 292 = 115 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (292 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_292 :
    recurrence5Scalar0Left.coeff 292 =
      -(((((3660950417136797782456355238891519697563937267266074188345148995693 * 10 ^ 70 +
        8323380143470537050939068060423344123730951749318567880932473242997704) * 10 ^ 70 +
        6746430114021603166082227213769554988673392199036257534686662749747495) * 10 ^ 70 +
        9238811325588571260128856267015345330474983279932809609584200826188265) * 10 ^ 70 +
        0383518542099395227104887862467447668965522826007183749294079157848247) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 293 = 116 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 15 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (293 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_293 :
    recurrence5Scalar0Left.coeff 293 =
      (((((2537532398636297395167548932158380729147816318269619584860336553624 * 10 ^ 70 +
        9592381319152757911006878317737912810887461881473216678591422269241780) * 10 ^ 70 +
        4079393758068618431788581635301182337220056301083122287414671975739896) * 10 ^ 70 +
        5787189026479902178855256351394867993462302205952396588856611425863996) * 10 ^ 70 +
        7245153196665178587215544335909952409417424859848465899263282216320298) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 294 = 117 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 14 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (294 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_294 :
    recurrence5Scalar0Left.coeff 294 =
      -(((((1640242036427899904768865484680469328670921625461414945345620603263 * 10 ^ 70 +
        2422894936774499144802770215324167285431935012496201117707726908014474) * 10 ^ 70 +
        1883214594598359053686785790780901173250291882098851117149820558072231) * 10 ^ 70 +
        5446868223827619628879610319262926057929029899514913361619921680013583) * 10 ^ 70 +
        9883200700259043981437003092605119505596393336133394269052173789581531) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 295 = 118 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 13 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (295 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_295 :
    recurrence5Scalar0Left.coeff 295 =
      (((((997929744970919459710014451842600553212480830438796766451635850229 * 10 ^ 70 +
        8944723241544046694358563545321018740484838663406824270181124816027303) * 10 ^ 70 +
        9550019770730221962978288013065703036850729287100907775199088457303685) * 10 ^ 70 +
        3731370916432686530897209457511247835497858213730403528722502828914821) * 10 ^ 70 +
        3408651770987541930979872941667751940875811868734807385704658956536119) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 296 = 119 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 12 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (296 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_296 :
    recurrence5Scalar0Left.coeff 296 =
      -(((((575376153586576889425316099223039360111900031267371201694827378293 * 10 ^ 70 +
        8240228642629763246526392782938202172068913782054349358735973167411272) * 10 ^ 70 +
        6173882512560822464189549186036547954158424224227732253911686624928861) * 10 ^ 70 +
        9472801634748307422842177320957735646566363315038357391578844190241413) * 10 ^ 70 +
        3431478408539607345481083482691086766943059292413788118205475882776604) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 297 = 120 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 11 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (297 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_297 :
    recurrence5Scalar0Left.coeff 297 =
      (((((315934772611205756294934653552582553562757463443827378733837514234 * 10 ^ 70 +
        6411626871848374841449149466441626854641198920386453086662745878277254) * 10 ^ 70 +
        7829495780668196359248529647231698652263661606159625571127822729924133) * 10 ^ 70 +
        0087756815839500655308059642974063747126493957343215644436835753228363) * 10 ^ 70 +
        1281684494078754235787266204185976032963240206919496504214416341291884) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 298 = 121 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 10 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (298 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_298 :
    recurrence5Scalar0Left.coeff 298 =
      -(((((165796818916898510212269817664861872994752555097837780074968989454 * 10 ^ 70 +
        0927385126521692511157051957565559044624551153707653614316003404872398) * 10 ^ 70 +
        1433484307643704405032971682488739501650628631935600575118642776814590) * 10 ^ 70 +
        0029200475665748276702538378810615408055140534126916116516421802273191) * 10 ^ 70 +
        1247785781164198300654483630254142840313300215504823643268230951180909) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 299 = 122 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 9 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (299 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_299 :
    recurrence5Scalar0Left.coeff 299 =
      (((((83376137178272288699650232526030323497360250752742917366326150219 * 10 ^ 70 +
        8397680736163653647407783643215270906241715185299654782247082465198579) * 10 ^ 70 +
        3256004689716995618333049388104307620225984000302266141836343145006981) * 10 ^ 70 +
        1469027031245630995844887656204577208375458104299609082158408965318022) * 10 ^ 70 +
        6812894075231694097461954276923471225294032992685796567895089552175511) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 300 = 123 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 8 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (300 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_300 :
    recurrence5Scalar0Left.coeff 300 =
      -(((((40268757034213267318446599749268741560652901504701992463127403572 * 10 ^ 70 +
        3402480370363223485913213380450016156163144064850250921843188152030049) * 10 ^ 70 +
        5139727937865087993818264493434498536928876215065961696066442425121974) * 10 ^ 70 +
        1136688227856030674216253913007123867119471370222129093520700703555271) * 10 ^ 70 +
        3418424450271009846365529667464030077640450284657610682900273012299495) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 301 = 124 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 7 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (301 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_301 :
    recurrence5Scalar0Left.coeff 301 =
      (((((18724216617516428253236266020236239223188391201411930404874933117 * 10 ^ 70 +
        5964973342893463036356964791164377267740687246703050688476900274846919) * 10 ^ 70 +
        8541966328186315318021276818612943114462976548869935878568906683552328) * 10 ^ 70 +
        3202215344930749894488271955440643546201886882010050373754575231802453) * 10 ^ 70 +
        6005904607500346737208140275500661967563317921861611475693425138662990) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 302 = 125 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 6 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (302 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_302 :
    recurrence5Scalar0Left.coeff 302 =
      -(((((8410886760660904068279510796437526983183616410136227173809841318 * 10 ^ 70 +
        1343700023189549530358515755989085200541798848641004359277562565536918) * 10 ^ 70 +
        0411940511855848248543572045286565180288398448672214738232935330643756) * 10 ^ 70 +
        7461412438370812318315766465557306997661576263895579265468314042662608) * 10 ^ 70 +
        8117180382503888902329507526366217698955932167862228677884537408469235) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 303 = 126 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 5 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (303 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_303 :
    recurrence5Scalar0Left.coeff 303 =
      (((((3671143590960913309875880466878569156179258894110125753758603685 * 10 ^ 70 +
        0423084131011028980491459235810093890781831442757895512915306550688503) * 10 ^ 70 +
        2840626761301935087909642879872667234041809609260025185424107551561289) * 10 ^ 70 +
        2597142144339838031595998570695923199397995060166731956220368906303064) * 10 ^ 70 +
        9193122333767165405253690735311415352737143289659942175724196635588139) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 304 = 127 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 4 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (304 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_304 :
    recurrence5Scalar0Left.coeff 304 =
      -(((((1572798341623594103198946790187366702624862624189548775720272086 * 10 ^ 70 +
        9505881463945774453360331286381346270501447893000108633550448193270531) * 10 ^ 70 +
        6646641776560085500458980712009600748421520328149428248151972005907127) * 10 ^ 70 +
        6332228226432136087322798974274557741670073802565875677554129751581216) * 10 ^ 70 +
        7079422672671950059629433799695714435664919875536303409852952867969084) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 305 = 128 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 3 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (305 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_305 :
    recurrence5Scalar0Left.coeff 305 =
      (((((672459471048328478921700308853627022793400896660847615746643313 * 10 ^ 70 +
        9597612307144331518444835607075334134450246484200583460701270923941980) * 10 ^ 70 +
        2164504907479373520184161895110802992938350672211663685983326463844103) * 10 ^ 70 +
        9579269627124312315675663355555205058748678150218713185660668799683854) * 10 ^ 70 +
        1016967696097556695280925075207796350379068765254961376580229628596371) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 306 = 129 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 2 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (306 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_306 :
    recurrence5Scalar0Left.coeff 306 =
      -(((((293789223423945766408982716220716045942181771665585798543026998 * 10 ^ 70 +
        0136408916069012103718124909978396907724126899673403483235279752811367) * 10 ^ 70 +
        8296336499452417105561751505432620481652009960262987950291297618620405) * 10 ^ 70 +
        6883299107668097140899967336590859385432011583830014707880427004165797) * 10 ^ 70 +
        0296232401616897125603826732525904743899474214504089136257457692175663) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 307 = 130 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 1 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
