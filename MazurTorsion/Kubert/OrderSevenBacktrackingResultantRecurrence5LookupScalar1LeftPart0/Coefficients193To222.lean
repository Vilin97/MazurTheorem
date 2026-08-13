/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar1LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1Left coefficient convolution

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
  recurrence5A1_coeff_0
  recurrence5A1_coeff_1
  recurrence5A1_coeff_2
  recurrence5A1_coeff_3
  recurrence5A1_coeff_4
  recurrence5A1_coeff_5
  recurrence5A1_coeff_6
  recurrence5A1_coeff_7
  recurrence5A1_coeff_8
  recurrence5A1_coeff_9
  recurrence5A1_coeff_10
  recurrence5A1_coeff_11
  recurrence5A1_coeff_12
  recurrence5A1_coeff_13
  recurrence5A1_coeff_14
  recurrence5A1_coeff_15
  recurrence5A1_coeff_16
  recurrence5A1_coeff_17
  recurrence5A1_coeff_18
  recurrence5A1_coeff_19
  recurrence5A1_coeff_20
  recurrence5A1_coeff_21
  recurrence5A1_coeff_22
  recurrence5A1_coeff_23
  recurrence5A1_coeff_24
  recurrence5A1_coeff_25
  recurrence5A1_coeff_26
  recurrence5A1_coeff_27
  recurrence5A1_coeff_28

attribute [local simp]
  recurrence5A1_coeff_29
  recurrence5A1_coeff_30
  recurrence5A1_coeff_31
  recurrence5A1_coeff_32
  recurrence5A1_coeff_33
  recurrence5A1_coeff_34
  recurrence5A1_coeff_35
  recurrence5A1_coeff_36
  recurrence5A1_coeff_37
  recurrence5A1_coeff_38
  recurrence5A1_coeff_39
  recurrence5A1_coeff_40
  recurrence5A1_coeff_41
  recurrence5A1_coeff_42
  recurrence5A1_coeff_43
  recurrence5A1_coeff_44
  recurrence5A1_coeff_45
  recurrence5A1_coeff_46
  recurrence5A1_coeff_47
  recurrence5A1_coeff_48
  recurrence5A1_coeff_49
  recurrence5A1_coeff_50
  recurrence5A1_coeff_51
  recurrence5A1_coeff_52
  recurrence5A1_coeff_53
  recurrence5A1_coeff_54
  recurrence5A1_coeff_55
  recurrence5A1_coeff_56
  recurrence5A1_coeff_57
  recurrence5A1_coeff_58
  recurrence5A1_coeff_59
  recurrence5A1_coeff_60
  recurrence5A1_coeff_61
  recurrence5A1_coeff_62
  recurrence5A1_coeff_63
  recurrence5A1_coeff_64
  recurrence5A1_coeff_65
  recurrence5A1_coeff_66
  recurrence5A1_coeff_67
  recurrence5A1_coeff_68
  recurrence5A1_coeff_69
  recurrence5A1_coeff_70
  recurrence5A1_coeff_71
  recurrence5A1_coeff_72
  recurrence5A1_coeff_73
  recurrence5A1_coeff_74
  recurrence5A1_coeff_75
  recurrence5A1_coeff_76
  recurrence5A1_coeff_77
  recurrence5A1_coeff_78
  recurrence5A1_coeff_79
  recurrence5A1_coeff_80
  recurrence5A1_coeff_81
  recurrence5A1_coeff_82
  recurrence5A1_coeff_83
  recurrence5A1_coeff_84
  recurrence5A1_coeff_85
  recurrence5A1_coeff_86
  recurrence5A1_coeff_87
  recurrence5A1_coeff_88
  recurrence5A1_coeff_89
  recurrence5A1_coeff_90
  recurrence5A1_coeff_91
  recurrence5A1_coeff_92

attribute [local simp]
  recurrence5A1_coeff_93
  recurrence5A1_coeff_94
  recurrence5A1_coeff_95
  recurrence5A1_coeff_96
  recurrence5A1_coeff_97
  recurrence5A1_coeff_98
  recurrence5A1_coeff_99
  recurrence5A1_coeff_100
  recurrence5A1_coeff_101
  recurrence5A1_coeff_102
  recurrence5A1_coeff_103
  recurrence5A1_coeff_104
  recurrence5A1_coeff_105
  recurrence5A1_coeff_106
  recurrence5A1_coeff_107
  recurrence5A1_coeff_108
  recurrence5A1_coeff_109
  recurrence5A1_coeff_110
  recurrence5A1_coeff_111
  recurrence5A1_coeff_112
  recurrence5A1_coeff_113
  recurrence5A1_coeff_114
  recurrence5A1_coeff_115
  recurrence5A1_coeff_116
  recurrence5A1_coeff_117
  recurrence5A1_coeff_118
  recurrence5A1_coeff_119
  recurrence5A1_coeff_120
  recurrence5A1_coeff_121
  recurrence5A1_coeff_122
  recurrence5A1_coeff_123
  recurrence5A1_coeff_124
  recurrence5A1_coeff_125
  recurrence5A1_coeff_126
  recurrence5A1_coeff_127
  recurrence5A1_coeff_128
  recurrence5A1_coeff_129
  recurrence5A1_coeff_130
  recurrence5A1_coeff_131
  recurrence5A1_coeff_132
  recurrence5A1_coeff_133
  recurrence5A1_coeff_134
  recurrence5A1_coeff_135
  recurrence5A1_coeff_136
  recurrence5A1_coeff_137
  recurrence5A1_coeff_138
  recurrence5A1_coeff_139
  recurrence5A1_coeff_140
  recurrence5A1_coeff_141
  recurrence5A1_coeff_142
  recurrence5A1_coeff_143
  recurrence5A1_coeff_144
  recurrence5A1_coeff_145
  recurrence5A1_coeff_146
  recurrence5A1_coeff_147
  recurrence5A1_coeff_148
  recurrence5A1_coeff_149
  recurrence5A1_coeff_150
  recurrence5A1_coeff_151
  recurrence5A1_coeff_152
  recurrence5A1_coeff_153
  recurrence5A1_coeff_154
  recurrence5A1_coeff_155
  recurrence5A1_coeff_156

attribute [local simp]
  recurrence5A1_coeff_157
  recurrence5A1_coeff_158
  recurrence5A1_coeff_159
  recurrence5A1_coeff_160
  recurrence5A1_coeff_161
  recurrence5A1_coeff_162
  recurrence5A1_coeff_163
  recurrence5A1_coeff_164
  recurrence5A1_coeff_165
  recurrence5A1_coeff_166
  recurrence5A1_coeff_167
  recurrence5A1_coeff_168
  recurrence5A1_coeff_169
  recurrence5A1_coeff_170
  recurrence5A1_coeff_171
  recurrence5A1_coeff_172

private theorem recurrence5Scalar1Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_193 :
    recurrence5Scalar1Left.coeff 193 =
      ((((((2970785218 * 10 ^ 70 +
        9958721733434232339443218813154970842480804192650266215862529918200782) * 10 ^ 70 +
        8006446947257157190212178833558795337017153582943699994587017092406573) * 10 ^ 70 +
        0555317638047378436665781862750646323826236232653216115389651977272100) * 10 ^ 70 +
        5845174925483012724289280838466781092221035716983336556761532341011777) * 10 ^ 70 +
        8287875598783038843072211690054107856355425037680808680395452636458418) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 21 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_193_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_194 :
    recurrence5Scalar1Left.coeff 194 =
      -((((((3838059910 * 10 ^ 70 +
        3031808923822866971124891715609948477642250870701863189885030375663416) * 10 ^ 70 +
        8210991754155336499821429399519277265230465131248519868938139959917416) * 10 ^ 70 +
        9645116098137510363533616295452135171743000385237774435616011334894672) * 10 ^ 70 +
        7520934703149013402152896508517970639935637231641740712388584817162875) * 10 ^ 70 +
        7452170252381825963092129223322374867280183945950331697660774849798693) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 22 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_194_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_195 :
    recurrence5Scalar1Left.coeff 195 =
      ((((((4873522965 * 10 ^ 70 +
        7259313961546992344960731376409399511806476338383039101255480103227203) * 10 ^ 70 +
        4240109290643811701818018162638632830264127164156658929101472414281030) * 10 ^ 70 +
        4424984207901516922689501547502274478919410241193300459648032755536070) * 10 ^ 70 +
        6855131121935380992991168823760454822930781896956272606203695901728657) * 10 ^ 70 +
        2167305623976856896307016634655158781219837360679754649495559187061635) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 23 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_195_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_196 :
    recurrence5Scalar1Left.coeff 196 =
      -((((((6082113400 * 10 ^ 70 +
        5736339350841993210994385234478108784592904118355303879583123728350794) * 10 ^ 70 +
        2618257651144835855376236984425242391093176284278379037494357626499947) * 10 ^ 70 +
        9384927749917024468298312143465041080847103746670287105741685984966353) * 10 ^ 70 +
        0501217738336475457862156999440256710708203164291810193522958994297178) * 10 ^ 70 +
        2220497322841985524516659987717460796418527918512804338704672451891026) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 24 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_196_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_197 :
    recurrence5Scalar1Left.coeff 197 =
      ((((((7459900207 * 10 ^ 70 +
        4704026290114958193365463802198474610988819666588996890695134527320914) * 10 ^ 70 +
        1538403161758673335999710772156025952347735099174032536652140733971087) * 10 ^ 70 +
        6760459580685988782170822642867584601841511247468282516912722826795404) * 10 ^ 70 +
        0922488570474394739354781081552976280063911802820413982539991928803110) * 10 ^ 70 +
        2205693332116837455548096274084176839520825257397315096981144665617006) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 25 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_197_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_198 :
    recurrence5Scalar1Left.coeff 198 =
      -((((((8992125056 * 10 ^ 70 +
        7227868584539047439045370557430167435906634618509689774002397267196057) * 10 ^ 70 +
        1957238211234689652471261843812014908790497680344170324795444128776411) * 10 ^ 70 +
        9844191760620342915151009061184787404827073238728508898945707422524713) * 10 ^ 70 +
        8508046095233023777543411294133187530520206778079468459498635904507974) * 10 ^ 70 +
        6514431022590020617499795521461717758547434314227067501109139228799467) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 26 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_198_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_199 :
    recurrence5Scalar1Left.coeff 199 =
      ((((((10651799012 * 10 ^ 70 +
        4217283577198090089162862588088820234846756033859360707290508908262001) * 10 ^ 70 +
        1959866456529589237909723189489925239939844969322742905862705333266991) * 10 ^ 70 +
        8116530703636953952898417834938841285375030692576598815325081628147438) * 10 ^ 70 +
        9741926538859736535084792387455126773335088944658958655402752202087361) * 10 ^ 70 +
        7529952942665461262449974703652607044604737155882770873311842640521821) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 27 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_199_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_200 :
    recurrence5Scalar1Left.coeff 200 =
      -((((((12399142582 * 10 ^ 70 +
        7705220671262025097937930517196102402066448722520043067983290694721358) * 10 ^ 70 +
        8740480869417744594608838381597027909680637336427442247982308911757295) * 10 ^ 70 +
        5792295687882874022791135083318208428765696196657808475192741429452334) * 10 ^ 70 +
        5265111800002389694320424864378634330815836688208534877981111359692666) * 10 ^ 70 +
        1340102618870379136360283340627521449475678678045031824487569873279575) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 28 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_200_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_201 :
    recurrence5Scalar1Left.coeff 201 =
      ((((((14182113536 * 10 ^ 70 +
        7454979246472530042358575638384040885979118070675473290295879221355902) * 10 ^ 70 +
        6688421418640335759354671430480282631714399420372959747186109147338705) * 10 ^ 70 +
        4083262903198952935219566738214029346628765711021069473901296362968840) * 10 ^ 70 +
        6927711112588468214622692876665643717978350927520227649096242366744774) * 10 ^ 70 +
        9560036074138257805693666773578057160038566093437686631622072600408375) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 29 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_201_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_202 :
    recurrence5Scalar1Left.coeff 202 =
      -((((((15938176265 * 10 ^ 70 +
        4727493264491200028427581930213306698189286703100184004556595246273455) * 10 ^ 70 +
        4515302123957354227390325860250222945204250049364308899462215592119101) * 10 ^ 70 +
        6290637420147061403043720961289186815775600495352352713695990476130123) * 10 ^ 70 +
        0435765116540452258687922827795996004631327059589205758006759755670620) * 10 ^ 70 +
        7738187384263229851975698670350551345359406954192205428439407022608606) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 30 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_202_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_203 :
    recurrence5Scalar1Left.coeff 203 =
      ((((((17597335518 * 10 ^ 70 +
        3664053495778763353182523058905752630682137831033729152367949510926229) * 10 ^ 70 +
        0062386055577726611142403214494616714872090646217888485388333821944528) * 10 ^ 70 +
        3474184965843377773834173914925342062631216211248636175064886336861405) * 10 ^ 70 +
        3906628090350253846904303905901653791949086905549144027447765298296649) * 10 ^ 70 +
        2194465196072922721633637095315028339072985794340408190981468134589761) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 31 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_203_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_204 :
    recurrence5Scalar1Left.coeff 204 =
      -((((((19086299928 * 10 ^ 70 +
        4719007419731700851625272439269565651454673064442232462045314179958961) * 10 ^ 70 +
        6187651102355959222152139720006806967547045364272148439463739712608782) * 10 ^ 70 +
        3878415975015330148590858361726994387376496331599516619873779285756627) * 10 ^ 70 +
        0201263865046807076224900856321694761204913870801418818655298371809055) * 10 ^ 70 +
        9854069137823906635137929872046777249839167477233720790757912480616319) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 32 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_204_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_205 :
    recurrence5Scalar1Left.coeff 205 =
      ((((((20333477877 * 10 ^ 70 +
        0780754384702656608337441862889594311906231328296005894540786040390159) * 10 ^ 70 +
        3040948420058792184422818147597742324691846760545446238467814049310273) * 10 ^ 70 +
        2509436971249528055905993959973023145920399363998991625032382892353857) * 10 ^ 70 +
        2745362119280667144028871754900065913444528328924416204084495443110023) * 10 ^ 70 +
        1870756954452847605921308000272027150756470909868746247552525317092124) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 33 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_205_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_206 :
    recurrence5Scalar1Left.coeff 206 =
      -((((((21274365246 * 10 ^ 70 +
        1928771579576181067904333474029189094963089384365952596527546744422815) * 10 ^ 70 +
        5006054034777229951284767793302870716872860400198996482287415574338443) * 10 ^ 70 +
        6381667421286649010508061872027775875614193289178450070603506252057624) * 10 ^ 70 +
        8667183630812417425193338458638959746022258943227502779678723978367554) * 10 ^ 70 +
        9966499080433230685979802852121930869382735993617111460917120723352809) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 34 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_206_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_207 :
    recurrence5Scalar1Left.coeff 207 =
      ((((((21856786812 * 10 ^ 70 +
        3597290782214578589873497715975025813259223496086890503730816041052469) * 10 ^ 70 +
        5797476706987025215244036942546672539541610714858195818087135166933329) * 10 ^ 70 +
        6570466570781327234565775382079032126133854900318397773961602492299010) * 10 ^ 70 +
        1090306444832963934315614447296110390531626519390123509156911030611838) * 10 ^ 70 +
        7106335633719992612394572736077928845752779510506198651313548324388868) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 35 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_207_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_208 :
    recurrence5Scalar1Left.coeff 208 =
      -((((((22045420958 * 10 ^ 70 +
        0810821222183551104124621339777340224771644359833758062155768915801441) * 10 ^ 70 +
        9057980063292805260297054208318675651383317133231689009469778287673907) * 10 ^ 70 +
        9435394557810601046880958779649637107089238208087272865924779763740288) * 10 ^ 70 +
        8125891711252391601249225613402060706213869869948866277981841456596537) * 10 ^ 70 +
        6571352997986762637977564844134887550910490904932106420880932358943672) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 36 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_208_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_209 :
    recurrence5Scalar1Left.coeff 209 =
      ((((((21825082244 * 10 ^ 70 +
        6447146541112483026515500188024368267467684386702439164885748695677008) * 10 ^ 70 +
        8858214712050617521498530601677702464442626388929877426527102830090008) * 10 ^ 70 +
        0338753670974556342819503109096899065526702233741090220893954928820168) * 10 ^ 70 +
        9492079578007906218861990204597471769963805098565867841106976048273335) * 10 ^ 70 +
        5716665984934019529047689386277929204052454716308227919472163748745517) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 37 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_209_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_210 :
    recurrence5Scalar1Left.coeff 210 =
      -((((((21202357140 * 10 ^ 70 +
        3413107336121068669073259831926005522016995889313462695600644950245628) * 10 ^ 70 +
        5514421947842583811346138518958037190676362541729113389281710740110925) * 10 ^ 70 +
        1924947374208946502823501119325114111343424616283662485564111476149443) * 10 ^ 70 +
        0199639273655341360026586345468142498166787209734983400890935673407972) * 10 ^ 70 +
        2024603746794692510119126535575983583572669129988994764182275137079666) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 38 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_210_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_211 :
    recurrence5Scalar1Left.coeff 211 =
      ((((((20205370726 * 10 ^ 70 +
        0357027450373992618238647366469506959351490415736321073253563342997831) * 10 ^ 70 +
        5361714319159367613775229174173975441377875092962078277269067999613237) * 10 ^ 70 +
        3991963775030979278386091215166255791068431803671083399485345325005127) * 10 ^ 70 +
        6845043936093718824748291798094797021919591511002032489816460574973899) * 10 ^ 70 +
        8120164931255406686162052723732733685602410036776723282377609242998611) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 39 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_211_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_212 :
    recurrence5Scalar1Left.coeff 212 =
      -((((((18881681195 * 10 ^ 70 +
        1722080085283005282009205624709317407219802226503730070723896727711525) * 10 ^ 70 +
        7964958856548754836007791506784537231356867123517942049304612524934963) * 10 ^ 70 +
        2794552725730187969905864831268471935017538114289745147463300812400249) * 10 ^ 70 +
        5855700368797556201305170158293476442207490534955519392417591377616782) * 10 ^ 70 +
        6219357850565027667395561303986091326768605359689390818332086555513125) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 40 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_212_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_213 :
    recurrence5Scalar1Left.coeff 213 =
      ((((((17294522097 * 10 ^ 70 +
        5759496915301812417530609101480759876298218925771322282249078116290207) * 10 ^ 70 +
        3274168915724157305680410686267435277508953719301380867017867739735249) * 10 ^ 70 +
        7854774084361968058954764234486840548489011187362046479936384544136640) * 10 ^ 70 +
        9822629436622569216343062112717215659162551298644391140206686380978866) * 10 ^ 70 +
        7769965046191021843342747234624107748263832073249409898695449776159906) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 41 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_213_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_214 :
    recurrence5Scalar1Left.coeff 214 =
      -((((((15517805932 * 10 ^ 70 +
        7457688403666448188637272821491791893708774112677580519471599864975659) * 10 ^ 70 +
        6066733270862857780069737316213139125848772943012393794104084682368095) * 10 ^ 70 +
        3608374215960965898238265259719040096101403899400645462208195838387652) * 10 ^ 70 +
        4277711820798194524886063188404518015272353651624997740421256958161324) * 10 ^ 70 +
        4264503406853231979939155212994775781847275131982562820276132082646061) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 42 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_214_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_215 :
    recurrence5Scalar1Left.coeff 215 =
      ((((((13630438083 * 10 ^ 70 +
        0949276178227424082627634799111686205747105719042109275034136728088166) * 10 ^ 70 +
        5856699669882939773048688327383287669273688117816708783030710538416175) * 10 ^ 70 +
        7925270567011975198512185974047723782155612232072055396876358024683713) * 10 ^ 70 +
        8473162345167222916815073336470152173343528648136929571574675501437426) * 10 ^ 70 +
        6406924209802656608087245435102824691989702262262072816931079892502386) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 43 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_215_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_216 :
    recurrence5Scalar1Left.coeff 216 =
      -((((((11710548385 * 10 ^ 70 +
        3658077047365930064872827670154717756406746346543067513500506025647655) * 10 ^ 70 +
        0075093149131475305366100530928058324853302628991824246836619815138097) * 10 ^ 70 +
        1844740381739697792526058889166430151997996531833130080954735808845507) * 10 ^ 70 +
        6611208242853564692935574857107990823580943240160430635793061650520918) * 10 ^ 70 +
        7557391598154973336244016049384345597930185016268861248308869085847790) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 44 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_216_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_217 :
    recurrence5Scalar1Left.coeff 217 =
      ((((((9830223211 * 10 ^ 70 +
        9688266258502024369788552973456468279503129143532246277172908159199040) * 10 ^ 70 +
        8156793668446174150402831653688698789850250690468278976432673179924159) * 10 ^ 70 +
        8566359389675192097001063034430438161169534040190118750769404092463666) * 10 ^ 70 +
        4493768061578358121674375497327306415194136155203192983561843798849049) * 10 ^ 70 +
        5662995157584418677886880654641846246555504380200475771224398459038115) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 45 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_217_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_218 :
    recurrence5Scalar1Left.coeff 218 =
      -((((((8051221786 * 10 ^ 70 +
        9481712379328808835967725297265230554147436576524262483804647213290881) * 10 ^ 70 +
        9805612114057939541325319804036612541325256989238774642238846179487807) * 10 ^ 70 +
        2019184998663205717106120078638943866478148628932177125894274790922879) * 10 ^ 70 +
        0607421346806586269529064472029096856256983303161138768416791877096962) * 10 ^ 70 +
        0549260006551320302407274419582591964315302322763763619610381562749374) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 46 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_218_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_219 :
    recurrence5Scalar1Left.coeff 219 =
      ((((((6422006151 * 10 ^ 70 +
        2049332713148589647440644140509934709576731291144117291992968330983099) * 10 ^ 70 +
        1264077722751181858003184066191082080194800854821694984743583234354218) * 10 ^ 70 +
        7902523939399608615418072339789560202596882893197006380549925449203392) * 10 ^ 70 +
        7990187936741601009490918879899992636875033636335898929853917244265434) * 10 ^ 70 +
        5517757556982167910271998666284978355012285645369731371441761720344756) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 47 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_219_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_220 :
    recurrence5Scalar1Left.coeff 220 =
      -((((((4976231616 * 10 ^ 70 +
        6641789918333244158588941607382349748543784833171151163610247232365763) * 10 ^ 70 +
        5374374691469292578780643568543456130963334998641366923884464959509456) * 10 ^ 70 +
        3748331796959868312287485679390801048044536723326168024532163487035731) * 10 ^ 70 +
        5437639116464986244106662861783164098350825894735483601105635839319727) * 10 ^ 70 +
        6376011116889451276317659564772705034793898181021419675244957143495894) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 48 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_220_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_221 :
    recurrence5Scalar1Left.coeff 221 =
      ((((((3732662665 * 10 ^ 70 +
        9717412388835706624024766190330828389445053517965929622488902514441154) * 10 ^ 70 +
        3892029122167822169141700496712129321225773018786640847955546220061869) * 10 ^ 70 +
        6474801047434676022986802303766319397260368215694487326070187867367492) * 10 ^ 70 +
        1528481690877186491924060311653052104943202772358945381886730277963984) * 10 ^ 70 +
        6529604913065745525615395030338536073507043823880055470104728994754274) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 49 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_221_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar1Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient1.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A1_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence5Scalar1Left_coeff_222 :
    recurrence5Scalar1Left.coeff 222 =
      -((((((2696323878 * 10 ^ 70 +
        0857603042550544811749488628655515456194835922758051207803597703021292) * 10 ^ 70 +
        3227305320129384222263081392166742282960388690528363347959069505383255) * 10 ^ 70 +
        0355218243979690683725095891601160508921057564529319366267916273372569) * 10 ^ 70 +
        4620053960508002371752460426739924925985076233314308661468689304078769) * 10 ^ 70 +
        3880737474691090819110195081632494068705521873716784247649798032114285) : ℚ) := by
  unfold recurrence5Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 223 = 50 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar1Left_coeff_222_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
