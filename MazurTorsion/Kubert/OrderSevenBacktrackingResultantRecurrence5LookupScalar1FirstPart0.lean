/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupB2A3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar1First coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5B0_coeff_0
  recurrence5B0_coeff_1
  recurrence5B0_coeff_2
  recurrence5B0_coeff_3
  recurrence5B0_coeff_4
  recurrence5B0_coeff_5
  recurrence5B0_coeff_6
  recurrence5B0_coeff_7
  recurrence5B0_coeff_8
  recurrence5B0_coeff_9
  recurrence5B0_coeff_10
  recurrence5B0_coeff_11
  recurrence5B0_coeff_12
  recurrence5B0_coeff_13
  recurrence5B0_coeff_14
  recurrence5B0_coeff_15
  recurrence5B0_coeff_16
  recurrence5B0_coeff_17
  recurrence5B0_coeff_18
  recurrence5B0_coeff_19
  recurrence5B0_coeff_20
  recurrence5B0_coeff_21
  recurrence5B0_coeff_22
  recurrence5B0_coeff_23
  recurrence5B0_coeff_24
  recurrence5B0_coeff_25
  recurrence5B0_coeff_26
  recurrence5B0_coeff_27
  recurrence5B0_coeff_28
  recurrence5B0_coeff_29
  recurrence5B0_coeff_30
  recurrence5B0_coeff_31
  recurrence5B0_coeff_32
  recurrence5B0_coeff_33
  recurrence5B0_coeff_34
  recurrence5B0_coeff_35
  recurrence5B0_coeff_36
  recurrence5B0_coeff_37
  recurrence5B0_coeff_38
  recurrence5B0_coeff_39
  recurrence5B0_coeff_40
  recurrence5B0_coeff_41
  recurrence5B0_coeff_42
  recurrence5B0_coeff_43
  recurrence5B0_coeff_44
  recurrence5B0_coeff_45
  recurrence5B0_coeff_46
  recurrence5B0_coeff_47
  recurrence5B0_coeff_48
  recurrence5B0_coeff_49
  recurrence5B0_coeff_50
  recurrence5B0_coeff_51
  recurrence5B0_coeff_52
  recurrence5B0_coeff_53
  recurrence5B0_coeff_54
  recurrence5B0_coeff_55
  recurrence5B0_coeff_56
  recurrence5B0_coeff_57
  recurrence5B0_coeff_58
  recurrence5B0_coeff_59
  recurrence5B0_coeff_60
  recurrence5B0_coeff_61
  recurrence5B0_coeff_62
  recurrence5B0_coeff_63

attribute [local simp]
  recurrence5B0_coeff_64
  recurrence5B0_coeff_65
  recurrence5B0_coeff_66
  recurrence5B0_coeff_67
  recurrence5B0_coeff_68
  recurrence5B0_coeff_69
  recurrence5B0_coeff_70
  recurrence5B0_coeff_71
  recurrence5B0_coeff_72
  recurrence5B0_coeff_73
  recurrence5B0_coeff_74
  recurrence5B0_coeff_75
  recurrence5B0_coeff_76
  recurrence5B0_coeff_77
  recurrence5B0_coeff_78
  recurrence5B0_coeff_79
  recurrence5B0_coeff_80
  recurrence5B0_coeff_81
  recurrence5B0_coeff_82
  recurrence5B0_coeff_83
  recurrence5B0_coeff_84
  recurrence5B0_coeff_85
  recurrence5B0_coeff_86
  recurrence5B0_coeff_87
  recurrence5B0_coeff_88
  recurrence5B0_coeff_89
  recurrence5B0_coeff_90
  recurrence5B0_coeff_91
  recurrence5B0_coeff_92
  recurrence5B0_coeff_93
  recurrence5B0_coeff_94
  recurrence5B0_coeff_95
  recurrence5B0_coeff_96
  recurrence5B0_coeff_97
  recurrence5B0_coeff_98
  recurrence5B0_coeff_99
  recurrence5B0_coeff_100
  recurrence5B0_coeff_101
  recurrence5B0_coeff_102
  recurrence5B0_coeff_103
  recurrence5B0_coeff_104
  recurrence5B0_coeff_105
  recurrence5B0_coeff_106
  recurrence5B0_coeff_107
  recurrence5B0_coeff_108
  recurrence5B0_coeff_109
  recurrence5B0_coeff_110
  recurrence5B0_coeff_111
  recurrence5B0_coeff_112
  recurrence5B0_coeff_113
  recurrence5B0_coeff_114
  recurrence5B0_coeff_115
  recurrence5B0_coeff_116
  recurrence5B0_coeff_117
  recurrence5B0_coeff_118
  recurrence5B0_coeff_119
  recurrence5B0_coeff_120
  recurrence5B0_coeff_121
  recurrence5B0_coeff_122
  recurrence5B0_coeff_123
  recurrence5B0_coeff_124
  recurrence5B0_coeff_125
  recurrence5B0_coeff_126
  recurrence5B0_coeff_127

attribute [local simp]
  recurrence5B0_coeff_128
  recurrence5B0_coeff_129
  recurrence5B0_coeff_130
  recurrence5B0_coeff_131
  recurrence5B0_coeff_132
  recurrence5B0_coeff_133
  recurrence5B0_coeff_134
  recurrence5B0_coeff_135
  recurrence5B0_coeff_136
  recurrence5B0_coeff_137
  recurrence5B0_coeff_138
  recurrence5B0_coeff_139
  recurrence5B0_coeff_140
  recurrence5B0_coeff_141
  recurrence5B0_coeff_142
  recurrence5B0_coeff_143
  recurrence5B0_coeff_144
  recurrence5B0_coeff_145
  recurrence5B0_coeff_146
  recurrence5B0_coeff_147
  recurrence5B0_coeff_148
  recurrence5B0_coeff_149
  recurrence5B0_coeff_150
  recurrence5B0_coeff_151
  recurrence5B0_coeff_152
  recurrence5B0_coeff_153
  recurrence5B2A3_coeff_0
  recurrence5B2A3_coeff_1
  recurrence5B2A3_coeff_2
  recurrence5B2A3_coeff_3
  recurrence5B2A3_coeff_4
  recurrence5B2A3_coeff_5
  recurrence5B2A3_coeff_6
  recurrence5B2A3_coeff_7
  recurrence5B2A3_coeff_8
  recurrence5B2A3_coeff_9
  recurrence5B2A3_coeff_10
  recurrence5B2A3_coeff_11
  recurrence5B2A3_coeff_12
  recurrence5B2A3_coeff_13
  recurrence5B2A3_coeff_14
  recurrence5B2A3_coeff_15
  recurrence5B2A3_coeff_16
  recurrence5B2A3_coeff_17
  recurrence5B2A3_coeff_18
  recurrence5B2A3_coeff_19
  recurrence5B2A3_coeff_20
  recurrence5B2A3_coeff_21
  recurrence5B2A3_coeff_22
  recurrence5B2A3_coeff_23
  recurrence5B2A3_coeff_24
  recurrence5B2A3_coeff_25
  recurrence5B2A3_coeff_26
  recurrence5B2A3_coeff_27
  recurrence5B2A3_coeff_28
  recurrence5B2A3_coeff_29
  recurrence5B2A3_coeff_30
  recurrence5B2A3_coeff_31
  recurrence5B2A3_coeff_32
  recurrence5B2A3_coeff_33
  recurrence5B2A3_coeff_34
  recurrence5B2A3_coeff_35
  recurrence5B2A3_coeff_36
  recurrence5B2A3_coeff_37

attribute [local simp]
  recurrence5B2A3_coeff_38
  recurrence5B2A3_coeff_39
  recurrence5B2A3_coeff_40
  recurrence5B2A3_coeff_41
  recurrence5B2A3_coeff_42
  recurrence5B2A3_coeff_43
  recurrence5B2A3_coeff_44
  recurrence5B2A3_coeff_45
  recurrence5B2A3_coeff_46
  recurrence5B2A3_coeff_47
  recurrence5B2A3_coeff_48
  recurrence5B2A3_coeff_49
  recurrence5B2A3_coeff_50
  recurrence5B2A3_coeff_51
  recurrence5B2A3_coeff_52
  recurrence5B2A3_coeff_53
  recurrence5B2A3_coeff_54
  recurrence5B2A3_coeff_55
  recurrence5B2A3_coeff_56
  recurrence5B2A3_coeff_57
  recurrence5B2A3_coeff_58
  recurrence5B2A3_coeff_59
  recurrence5B2A3_coeff_60
  recurrence5B2A3_coeff_61
  recurrence5B2A3_coeff_62
  recurrence5B2A3_coeff_63
  recurrence5B2A3_coeff_64
  recurrence5B2A3_coeff_65
  recurrence5B2A3_coeff_66
  recurrence5B2A3_coeff_67
  recurrence5B2A3_coeff_68
  recurrence5B2A3_coeff_69
  recurrence5B2A3_coeff_70
  recurrence5B2A3_coeff_71
  recurrence5B2A3_coeff_72
  recurrence5B2A3_coeff_73
  recurrence5B2A3_coeff_74
  recurrence5B2A3_coeff_75
  recurrence5B2A3_coeff_76
  recurrence5B2A3_coeff_77
  recurrence5B2A3_coeff_78
  recurrence5B2A3_coeff_79
  recurrence5B2A3_coeff_80
  recurrence5B2A3_coeff_81
  recurrence5B2A3_coeff_82
  recurrence5B2A3_coeff_83
  recurrence5B2A3_coeff_84
  recurrence5B2A3_coeff_85
  recurrence5B2A3_coeff_86
  recurrence5B2A3_coeff_87
  recurrence5B2A3_coeff_88
  recurrence5B2A3_coeff_89
  recurrence5B2A3_coeff_90
  recurrence5B2A3_coeff_91
  recurrence5B2A3_coeff_92
  recurrence5B2A3_coeff_93
  recurrence5B2A3_coeff_94
  recurrence5B2A3_coeff_95
  recurrence5B2A3_coeff_96
  recurrence5B2A3_coeff_97
  recurrence5B2A3_coeff_98
  recurrence5B2A3_coeff_99
  recurrence5B2A3_coeff_100
  recurrence5B2A3_coeff_101

attribute [local simp]
  recurrence5B2A3_coeff_102
  recurrence5B2A3_coeff_103
  recurrence5B2A3_coeff_104
  recurrence5B2A3_coeff_105
  recurrence5B2A3_coeff_106
  recurrence5B2A3_coeff_107
  recurrence5B2A3_coeff_108
  recurrence5B2A3_coeff_109
  recurrence5B2A3_coeff_110
  recurrence5B2A3_coeff_111
  recurrence5B2A3_coeff_112
  recurrence5B2A3_coeff_113
  recurrence5B2A3_coeff_114
  recurrence5B2A3_coeff_115
  recurrence5B2A3_coeff_116
  recurrence5B2A3_coeff_117
  recurrence5B2A3_coeff_118
  recurrence5B2A3_coeff_119
  recurrence5B2A3_coeff_120
  recurrence5B2A3_coeff_121
  recurrence5B2A3_coeff_122
  recurrence5B2A3_coeff_123
  recurrence5B2A3_coeff_124
  recurrence5B2A3_coeff_125
  recurrence5B2A3_coeff_126
  recurrence5B2A3_coeff_127
  recurrence5B2A3_coeff_128
  recurrence5B2A3_coeff_129
  recurrence5B2A3_coeff_130
  recurrence5B2A3_coeff_131
  recurrence5B2A3_coeff_132
  recurrence5B2A3_coeff_133
  recurrence5B2A3_coeff_134
  recurrence5B2A3_coeff_135
  recurrence5B2A3_coeff_136
  recurrence5B2A3_coeff_137
  recurrence5B2A3_coeff_138
  recurrence5B2A3_coeff_139
  recurrence5B2A3_coeff_140
  recurrence5B2A3_coeff_141
  recurrence5B2A3_coeff_142
  recurrence5B2A3_coeff_143
  recurrence5B2A3_coeff_144
  recurrence5B2A3_coeff_145
  recurrence5B2A3_coeff_146
  recurrence5B2A3_coeff_147
  recurrence5B2A3_coeff_148
  recurrence5B2A3_coeff_149
  recurrence5B2A3_coeff_150
  recurrence5B2A3_coeff_151
  recurrence5B2A3_coeff_152
  recurrence5B2A3_coeff_153
  recurrence5B2A3_coeff_154
  recurrence5B2A3_coeff_155
  recurrence5B2A3_coeff_156
  recurrence5B2A3_coeff_157
  recurrence5B2A3_coeff_158
  recurrence5B2A3_coeff_159
  recurrence5B2A3_coeff_160
  recurrence5B2A3_coeff_161
  recurrence5B2A3_coeff_162
  recurrence5B2A3_coeff_163
  recurrence5B2A3_coeff_164
  recurrence5B2A3_coeff_165

attribute [local simp]
  recurrence5B2A3_coeff_166
  recurrence5B2A3_coeff_167
  recurrence5B2A3_coeff_168
  recurrence5B2A3_coeff_169
  recurrence5B2A3_coeff_170
  recurrence5B2A3_coeff_171
  recurrence5B2A3_coeff_172
  recurrence5B2A3_coeff_173
  recurrence5B2A3_coeff_174
  recurrence5B2A3_coeff_175
  recurrence5B2A3_coeff_176
  recurrence5B2A3_coeff_177
  recurrence5B2A3_coeff_178
  recurrence5B2A3_coeff_179
  recurrence5B2A3_coeff_180
  recurrence5B2A3_coeff_181
  recurrence5B2A3_coeff_182
  recurrence5B2A3_coeff_183
  recurrence5B2A3_coeff_184
  recurrence5B2A3_coeff_185
  recurrence5B2A3_coeff_186
  recurrence5B2A3_coeff_187
  recurrence5B2A3_coeff_188
  recurrence5B2A3_coeff_189
  recurrence5B2A3_coeff_190
  recurrence5B2A3_coeff_191
  recurrence5B2A3_coeff_192
  recurrence5B2A3_coeff_193
  recurrence5B2A3_coeff_194
  recurrence5B2A3_coeff_195
  recurrence5B2A3_coeff_196
  recurrence5B2A3_coeff_197
  recurrence5B2A3_coeff_198
  recurrence5B2A3_coeff_199
  recurrence5B2A3_coeff_200
  recurrence5B2A3_coeff_201
  recurrence5B2A3_coeff_202
  recurrence5B2A3_coeff_203
  recurrence5B2A3_coeff_204
  recurrence5B2A3_coeff_205
  recurrence5B2A3_coeff_206
  recurrence5B2A3_coeff_207
  recurrence5B2A3_coeff_208
  recurrence5B2A3_coeff_209
  recurrence5B2A3_coeff_210
  recurrence5B2A3_coeff_211
  recurrence5B2A3_coeff_212
  recurrence5B2A3_coeff_213
  recurrence5B2A3_coeff_214
  recurrence5B2A3_coeff_215
  recurrence5B2A3_coeff_216
  recurrence5B2A3_coeff_217
  recurrence5B2A3_coeff_218
  recurrence5B2A3_coeff_219
  recurrence5B2A3_coeff_220
  recurrence5B2A3_coeff_221
  recurrence5B2A3_coeff_222
  recurrence5B2A3_coeff_223
  recurrence5B2A3_coeff_224
  recurrence5B2A3_coeff_225
  recurrence5B2A3_coeff_226
  recurrence5B2A3_coeff_227
  recurrence5B2A3_coeff_228
  recurrence5B2A3_coeff_229

attribute [local simp]
  recurrence5B2A3_coeff_230
  recurrence5B2A3_coeff_231
  recurrence5B2A3_coeff_232
  recurrence5B2A3_coeff_233
  recurrence5B2A3_coeff_234
  recurrence5B2A3_coeff_235
  recurrence5B2A3_coeff_236
  recurrence5B2A3_coeff_237
  recurrence5B2A3_coeff_238
  recurrence5B2A3_coeff_239
  recurrence5B2A3_coeff_240
  recurrence5B2A3_coeff_241
  recurrence5B2A3_coeff_242
  recurrence5B2A3_coeff_243
  recurrence5B2A3_coeff_244
  recurrence5B2A3_coeff_245
  recurrence5B2A3_coeff_246
  recurrence5B2A3_coeff_247
  recurrence5B2A3_coeff_248
  recurrence5B2A3_coeff_249
  recurrence5B2A3_coeff_250
  recurrence5B2A3_coeff_251
  recurrence5B2A3_coeff_252
  recurrence5B2A3_coeff_253
  recurrence5B2A3_coeff_254
  recurrence5B2A3_coeff_255
  recurrence5B2A3_coeff_256
  recurrence5B2A3_coeff_257
  recurrence5B2A3_coeff_258
  recurrence5B2A3_coeff_259
  recurrence5B2A3_coeff_260
  recurrence5B2A3_coeff_261
  recurrence5B2A3_coeff_262
  recurrence5B2A3_coeff_263
  recurrence5B2A3_coeff_264
  recurrence5B2A3_coeff_265
  recurrence5B2A3_coeff_266
  recurrence5B2A3_coeff_267
  recurrence5B2A3_coeff_268
  recurrence5B2A3_coeff_269
  recurrence5B2A3_coeff_270
  recurrence5B2A3_coeff_271
  recurrence5B2A3_coeff_272
  recurrence5B2A3_coeff_273
  recurrence5B2A3_coeff_274
  recurrence5B2A3_coeff_275
  recurrence5B2A3_coeff_276
  recurrence5B2A3_coeff_277
  recurrence5B2A3_coeff_278
  recurrence5B2A3_coeff_279
  recurrence5B2A3_coeff_280
  recurrence5B2A3_coeff_281
  recurrence5B2A3_coeff_282
  recurrence5B2A3_coeff_283
  recurrence5B2A3_coeff_284
  recurrence5B2A3_coeff_285
  recurrence5B2A3_coeff_286
  recurrence5B2A3_coeff_287
  recurrence5B2A3_coeff_288
  recurrence5B2A3_coeff_289
  recurrence5B2A3_coeff_290
  recurrence5B2A3_coeff_291
  recurrence5B2A3_coeff_292
  recurrence5B2A3_coeff_293

attribute [local simp]
  recurrence5B2A3_coeff_294
  recurrence5B2A3_coeff_295
  recurrence5B2A3_coeff_296
  recurrence5B2A3_coeff_297
  recurrence5B2A3_coeff_298
  recurrence5B2A3_coeff_299
  recurrence5B2A3_coeff_300
  recurrence5B2A3_coeff_301
  recurrence5B2A3_coeff_302
  recurrence5B2A3_coeff_303
  recurrence5B2A3_coeff_304
  recurrence5B2A3_coeff_305
  recurrence5B2A3_coeff_306
  recurrence5B2A3_coeff_307
  recurrence5B2A3_coeff_308
  recurrence5B2A3_coeff_309

theorem recurrence5Scalar1First_coeff_0 :
    recurrence5Scalar1First.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_1 :
    recurrence5Scalar1First.coeff 1 =
      ((3960986350084465496212773693154494720861151037798706032 * 10 ^ 70 +
        6934766566837676783328683440136112803279151052721015997562404672962560) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_2 :
    recurrence5Scalar1First.coeff 2 =
      ((6121104305145715563987169105795026490955454332160381291249 * 10 ^ 70 +
        2230948071051854566503516265035807714607666646098155894707542104797184) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_3 :
    recurrence5Scalar1First.coeff 3 =
      ((4527563013245905018508116420078064110317188804485783980465044 * 10 ^ 70 +
        5713722418991515939245988044788715214927610101697681669000875982278144) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_4 :
    recurrence5Scalar1First.coeff 4 =
      ((34443874142356232608457349521661412932320190102372297271987880628 * 10 ^ 70 +
        1488794522583179871134736486054398451636434068645453358777651311889280) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_5 :
    recurrence5Scalar1First.coeff 5 =
      -((403735184078136551894736198648552898491289264080644576619351582125126 * 10 ^ 70 +
        0414478707527572136133640603686702791227423443359006403194973210453280) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_6 :
    recurrence5Scalar1First.coeff 6 =
      (((148 * 10 ^ 70 +
        6394903092492982130361187801834496740581001564775192035109431283714132) * 10 ^ 70 +
        8729059432292259319998122825148891050099838448780037941542754468856736) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_7 :
    recurrence5Scalar1First.coeff 7 =
      -(((324826 * 10 ^ 70 +
        0463996382494496166975047218677314553636177472331143306268481395848472) * 10 ^ 70 +
        0895690932457221952256258961693554283363741472228758081087908104586976) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_8 :
    recurrence5Scalar1First.coeff 8 =
      (((503424008 * 10 ^ 70 +
        4990942632162259277031301866470459862416079644087545726811160723163241) * 10 ^ 70 +
        3181410780756698817323768297410695130257546922186513207271723152660288) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_9 :
    recurrence5Scalar1First.coeff 9 =
      -(((566618525742 * 10 ^ 70 +
        2769101745299145153677030548196989504048040373435051258762871120282452) * 10 ^ 70 +
        0305710223584769924021059404502327552759987066239363709919709990093792) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_10 :
    recurrence5Scalar1First.coeff 10 =
      (((459085524698204 * 10 ^ 70 +
        8758020791878931177809980755580636636693993717567912588795489489492423) * 10 ^ 70 +
        5041390119481370646114151486910874921488352274341705758938553436405032) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_11 :
    recurrence5Scalar1First.coeff 11 =
      -(((245728536595567965 * 10 ^ 70 +
        4072877451868470177494778407494529293850011773843594650261851807208506) * 10 ^ 70 +
        4534167080757089765104544512639588872688954354554623964986217468620072) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_12 :
    recurrence5Scalar1First.coeff 12 =
      (((51188347643019240278 * 10 ^ 70 +
        2854756930130414808377155946864449708735353480106749576717118297442582) * 10 ^ 70 +
        0875607129085668027061158643990334799656655240946159283163497360517088) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_13 :
    recurrence5Scalar1First.coeff 13 =
      (((48428012037528475893047 * 10 ^ 70 +
        4369575928667682447417885770385979403411896238509370856521568918317640) * 10 ^ 70 +
        3181451606586488527137197139937498516270592498310223074637653337230624) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_14 :
    recurrence5Scalar1First.coeff 14 =
      -(((62838686088341942999670454 * 10 ^ 70 +
        3651521586345447589293300169824525757682600150491820865149769031345486) * 10 ^ 70 +
        4800954978411671895021621253773457597014749632346859704603249467812072) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_15 :
    recurrence5Scalar1First.coeff 15 =
      (((40887329482945059223815185119 * 10 ^ 70 +
        5585094909538116544758878269878016464528661372853795175457163159443041) * 10 ^ 70 +
        3700721313612838499864258123392477994917774905896742545487628278578820) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_16 :
    recurrence5Scalar1First.coeff 16 =
      -(((18213472369957942126916806556581 * 10 ^ 70 +
        9826442144777580177870771338402170212768633016282613294529071017759819) * 10 ^ 70 +
        4802715124857386846971225223166490626241706091706139501418387102296192) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_17 :
    recurrence5Scalar1First.coeff 17 =
      (((5396051681861922511640955611716335 * 10 ^ 70 +
        0943044299984255608112449319485419262106765979339982316018151027385474) * 10 ^ 70 +
        2578498585792692632529686519073247995584868574745849253973756988599328) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_18 :
    recurrence5Scalar1First.coeff 18 =
      -(((306728190244651717512659476284031291 * 10 ^ 70 +
        1815541920099294505633433346933114127493432308713210699112779629744113) * 10 ^ 70 +
        5254583527397753735748626042821151998986794615068634926703658360268392) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_19 :
    recurrence5Scalar1First.coeff 19 =
      -(((980792593110300524345485618587792946826 * 10 ^ 70 +
        6994112511847696957598989924313538131523694940305238485048889117370317) * 10 ^ 70 +
        8522781895666731641803418640473168942082758892168487137121211684384406) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_20 :
    recurrence5Scalar1First.coeff 20 =
      (((883477088041308659738658031545077484408768 * 10 ^ 70 +
        6057262937759612480997143484470095388594372428915585780855545868887881) * 10 ^ 70 +
        7749058842140424481422086939232267695048202219541831851336012937032824) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_21 :
    recurrence5Scalar1First.coeff 21 =
      -(((497509480010138404281530442476775654605338850 * 10 ^ 70 +
        0223799231374925268568002949632675856096797128079160031853992675954086) * 10 ^ 70 +
        0248873992142839909104327419716281837064522770632792445570620440733152) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_22 :
    recurrence5Scalar1First.coeff 22 =
      (((205232354246448272545165743052632814005561744132 * 10 ^ 70 +
        5856758131086318198111390851323008101298467871929136071572016958621783) * 10 ^ 70 +
        3024404944426955429781001363079991566675810381379522379495971922490318) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_23 :
    recurrence5Scalar1First.coeff 23 =
      -(((60188802338685149139937159985286260591372371174153 * 10 ^ 70 +
        2665870071561605357952887999629897013890115941816052402959832516533904) * 10 ^ 70 +
        0031642605149062735292479433403373640678943267140237568062413057013026) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_24 :
    recurrence5Scalar1First.coeff 24 =
      (((9057918998844341710574745401844925336990517274653360 * 10 ^ 70 +
        7195156094303959751271919500982615731735039468308714209324329452480563) * 10 ^ 70 +
        5920166196050446283319548025618080076187076403614621417563638162264485) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_25 :
    recurrence5Scalar1First.coeff 25 =
      (((2339020828453280077273215594659853403631670480970038342 * 10 ^ 70 +
        0786816374812940422835140896726604781662384454753967428270909196625261) * 10 ^ 70 +
        0559992016198599526659322235389285853134773425553574613629348600205264) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_26 :
    recurrence5Scalar1First.coeff 26 =
      -(((2470975232547029616327582452315858914976323248036268856463 * 10 ^ 70 +
        0683642667443710378165885409308651919066609839924363283172281480849496) * 10 ^ 70 +
        8556027599234220357448170332230656452651223866588906454483897847790984) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_27 :
    recurrence5Scalar1First.coeff 27 =
      (((1164588388531886631364863772022745023195388294976588790433532 * 10 ^ 70 +
        4262966080295295373673567935284184787287533459065037684108437254526507) * 10 ^ 70 +
        6509946253722465671285719818162051457662763521234269561250808343545141) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_28 :
    recurrence5Scalar1First.coeff 28 =
      -(((405298501719560200698162768124247416593424479228277550378310169 * 10 ^ 70 +
        4093357661605639738283760183112423122486354652423262749849912636382372) * 10 ^ 70 +
        5040164230139319047033802073503645493634851913970582929834312791248616) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_29 :
    recurrence5Scalar1First.coeff 29 =
      (((115440736775970102988118953559666064283759280582233309619888385230 * 10 ^ 70 +
        9171306001734699710333836456339298607502142848683995567182331257076224) * 10 ^ 70 +
        6616572537001563590278680973028890625794557923236769531722158643815327) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_30 :
    recurrence5Scalar1First.coeff 30 =
      -(((28028063324470515832594407147765559923708589392456627786367361727789 * 10 ^ 70 +
        3323544599067384096859005448921089303639383691589739203702059141850237) * 10 ^ 70 +
        8808097948322119508117250043665563443859111359044116539501683166746673) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_31 :
    recurrence5Scalar1First.coeff 31 =
      (((5921438771943542781558892966055479758847021656606864885161482241056049 * 10 ^ 70 +
        6768905840933346495001483426277856347527088689513597451783508470942639) * 10 ^ 70 +
        4570917985139493690872348960755533941986914803277083438284630832023875) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_32 :
    recurrence5Scalar1First.coeff 32 =
      -((((110 * 10 ^ 70 +
        1202323732528856411520401880111643779356690344088368570509954930205443) * 10 ^ 70 +
        6404257122708621059908501872170262161515037024134544023891040192972761) * 10 ^ 70 +
        2698683559766643715653368972896986758950264846782152507464390567500545) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_33 :
    recurrence5Scalar1First.coeff 33 =
      ((((18137 * 10 ^ 70 +
        9879579029761155540218035346640643181758463638485764488660280875277642) * 10 ^ 70 +
        7496993534422425470323391680947002331722351158993275230153557999656822) * 10 ^ 70 +
        8015862678732129752304608893042203685264128082187216293085832645676238) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_34 :
    recurrence5Scalar1First.coeff 34 =
      -((((2651138 * 10 ^ 70 +
        9461416302794677210635673815207810689447192272998800406948035550992073) * 10 ^ 70 +
        2086517271107226016359804721294402382465989564565557372472834047257766) * 10 ^ 70 +
        9423236288443349900235690222801120583847314864191598167402925550531045) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_35 :
    recurrence5Scalar1First.coeff 35 =
      ((((342938943 * 10 ^ 70 +
        8817985319697776310119632142690501156975076042489789525261171287862698) * 10 ^ 70 +
        7916970916573696926150852176714725300989621314232169286834001654419337) * 10 ^ 70 +
        4859040682967585639204841886065019600930476984212416794176941983275219) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_36 :
    recurrence5Scalar1First.coeff 36 =
      -((((38876673352 * 10 ^ 70 +
        6591826045002447373421904609315513027449418912295085952174511764940328) * 10 ^ 70 +
        4658767923316299772225176100303105043014151675859684908985486738950756) * 10 ^ 70 +
        1128261009664269776427836970479273067790782101458514850265920776136806) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_37 :
    recurrence5Scalar1First.coeff 37 =
      ((((3770282608470 * 10 ^ 70 +
        4929330151449704545397019053151437521867188653407122182066011264701368) * 10 ^ 70 +
        4380000098617033803894361463218418587810101413323286304204520708387078) * 10 ^ 70 +
        0326143873240596219798489260643162659419168770827684188183048065928575) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_38 :
    recurrence5Scalar1First.coeff 38 =
      -((((293584645216586 * 10 ^ 70 +
        3465984671902181070237282853816610923904372050736692710678036205203844) * 10 ^ 70 +
        8669182866316179751951294900402595647393990118588572286630383628654571) * 10 ^ 70 +
        6109420301866021277222191185729194668284565001339001469923864103822757) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_39 :
    recurrence5Scalar1First.coeff 39 =
      ((((14403803540378230 * 10 ^ 70 +
        2628024412152196832624656990007802303496069562897027281936721231839642) * 10 ^ 70 +
        0919411440113107324283287261172039842913875551275418203971202032317932) * 10 ^ 70 +
        3446924404028469899175561615255406696037676875628942389817616552521697) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_40 :
    recurrence5Scalar1First.coeff 40 =
      ((((454238268690551916 * 10 ^ 70 +
        7815097069685661658780215596912025386940700068992698494800774380491596) * 10 ^ 70 +
        5063292281207631028390633061788984523408038714835649252060157958418000) * 10 ^ 70 +
        1771500977144865409557171654275000375617566797452183566405931976201379) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_41 :
    recurrence5Scalar1First.coeff 41 =
      -((((235897665552875138218 * 10 ^ 70 +
        9660685735078466993453769014241788834792639133153686286036426625128197) * 10 ^ 70 +
        5961924431385476573163342187816526405622299459306197835867684515682291) * 10 ^ 70 +
        8690262601925114976199287612085461724257144509495656715340779660954060) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_42 :
    recurrence5Scalar1First.coeff 42 =
      ((((38893077974508376252047 * 10 ^ 70 +
        0265590615932213890327466465359334993768330426391696663809552400411185) * 10 ^ 70 +
        8539491509428737978606454794053491898887846030000171453176620171045664) * 10 ^ 70 +
        2682575806697717409099348919151291818204430069368407056895011110808450) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_43 :
    recurrence5Scalar1First.coeff 43 =
      -((((4788591736927778277467106 * 10 ^ 70 +
        1726619654110523191887613525037958107107228726677878798897066554033747) * 10 ^ 70 +
        5064079090217652262748550882472733007950712612208226122819830324246265) * 10 ^ 70 +
        4332072132832134670579456799458372970837503419417627272680842773056434) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_44 :
    recurrence5Scalar1First.coeff 44 =
      ((((499061824375158682690688110 * 10 ^ 70 +
        2366312929533541458472850669661338339259981087395917050558771076709729) * 10 ^ 70 +
        4691092021809312760333401081840061030320430842922640560659651595274898) * 10 ^ 70 +
        7847943243710137497076761061949758416980233078513342592327099471918451) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_45 :
    recurrence5Scalar1First.coeff 45 =
      -((((46045407406706382329753357922 * 10 ^ 70 +
        9897688405401264273441529325738014598200763350670892020628389262031307) * 10 ^ 70 +
        6973186540451090459731637303380533181826948566095556311296452096888718) * 10 ^ 70 +
        3439321426051070247214357180919640433791816572396960477659463146652637) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_46 :
    recurrence5Scalar1First.coeff 46 =
      ((((3843775868956001368076481769249 * 10 ^ 70 +
        8053157693549075573937926270850287676019238224577638881360216911414632) * 10 ^ 70 +
        5906670408461956844467073164850236793290494878511688744236815669032339) * 10 ^ 70 +
        8736596258168319389865881420617522101154237587318293553056304752094439) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_47 :
    recurrence5Scalar1First.coeff 47 =
      -((((293981034358649263587467641162918 * 10 ^ 70 +
        5823988540991488589005140964826603914348473882603090937266301933724938) * 10 ^ 70 +
        4001983932555827694011080593435634583057064204501621373271060639991028) * 10 ^ 70 +
        6935422562527916696466482588142587808078377824389180068280917297084765) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_48 :
    recurrence5Scalar1First.coeff 48 =
      ((((20767709032205653952164986630934088 * 10 ^ 70 +
        4004332750190903522581003645945141587054207265739168745423237267276628) * 10 ^ 70 +
        7688022482503051049382641477763219348715287777062841375397574858582987) * 10 ^ 70 +
        6584263596247808116917720578563114874008262514739803264972994801947523) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_49 :
    recurrence5Scalar1First.coeff 49 =
      -((((1362790271535493778177062228942619702 * 10 ^ 70 +
        2075727368973898411501924917211694860987864310308878407267556795939798) * 10 ^ 70 +
        4301906574871200206183428290248583644758837286624766157972452258808987) * 10 ^ 70 +
        9347275886268940934004569610003552970691707210706674535934242790352800) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_50 :
    recurrence5Scalar1First.coeff 50 =
      ((((83420347013548747263140872439839273231 * 10 ^ 70 +
        0897876576055786598834687073117784745005327175502088377535783780634798) * 10 ^ 70 +
        3719700298239929618575613944773567653788705483575749135220966964861441) * 10 ^ 70 +
        7547149550511781006394892050529916067132255234336083193615038766415441) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_51 :
    recurrence5Scalar1First.coeff 51 =
      -((((4779064412947411819804449568299858942884 * 10 ^ 70 +
        3307537426055729871046927181218593052337813831220173250564813200146625) * 10 ^ 70 +
        7629590365318088973957873711531814643410634692834959619275836830253497) * 10 ^ 70 +
        3571688834511205292207473591901701552453210458636503515657634621026322) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_52 :
    recurrence5Scalar1First.coeff 52 =
      ((((256915668395740732402092443019595354047518 * 10 ^ 70 +
        0736523832731759971671986974796057783540369025627132541157022736107764) * 10 ^ 70 +
        1854163770121897342738379710384157790834364236443625059549048817942036) * 10 ^ 70 +
        3575189161334616552947471441225434325253185497068409600874854949168246) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_53 :
    recurrence5Scalar1First.coeff 53 =
      -((((12988711494274604655399289769166686527339733 * 10 ^ 70 +
        3107096808688706017064302001725260562419085081824271682892555871955490) * 10 ^ 70 +
        5751842298131750117421020430684102484676675306402627750935413654544895) * 10 ^ 70 +
        9217465889155153535405763580341227828181607016456334689250249959460249) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_54 :
    recurrence5Scalar1First.coeff 54 =
      ((((618688600179571639080383986358864924155471182 * 10 ^ 70 +
        5615177024791637522850065711596944473610610682679890491350682471126858) * 10 ^ 70 +
        8010839697957866654279046955491687054647715037180247054379991270017864) * 10 ^ 70 +
        2724088700749260263121490193045233760801948372867252479913246182809998) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_55 :
    recurrence5Scalar1First.coeff 55 =
      -((((27809671798936833692445859126697673158738409708 * 10 ^ 70 +
        6047461612201710159149434644105429808280373417956715963193507813606142) * 10 ^ 70 +
        6702371982059624449106334662759765000703146646617386648843142179305103) * 10 ^ 70 +
        2744092548482401541150352513626142932467394290069286862070262216324484) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_56 :
    recurrence5Scalar1First.coeff 56 =
      ((((1181218976080300824753561858832989559742148617543 * 10 ^ 70 +
        8711490719503199527594595483792035261889631886016974785114398760974003) * 10 ^ 70 +
        8887744714474649566262019111446853396586652646557927388107355830812526) * 10 ^ 70 +
        2546985861209879348044745318948898537739314418399686668770123419941240) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_57 :
    recurrence5Scalar1First.coeff 57 =
      -((((47466710777303782263165156228027400846977888746461 * 10 ^ 70 +
        6996440745397886110771902383231687580952054563710770524026221877291954) * 10 ^ 70 +
        4122306970713844992776783301308266640799231269171317121762009039461046) * 10 ^ 70 +
        0532529772793749140225505316229603440324178785946036227020294905697823) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_58 :
    recurrence5Scalar1First.coeff 58 =
      ((((1806403671921233441988384996181992708156254560008977 * 10 ^ 70 +
        2262688477577248989884093216645309738142492586480570989663431369443565) * 10 ^ 70 +
        2821822102715999419043533206393861573848565051213232230051000339577082) * 10 ^ 70 +
        1453701694767812581873335036399492798682647157347717462497087733628797) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_59 :
    recurrence5Scalar1First.coeff 59 =
      -((((65160549580059828553051055459598954308504798418533410 * 10 ^ 70 +
        6225221795725246683990341750000643922570869590990442774733712207206625) * 10 ^ 70 +
        6294830978019737042161958342064061184740882547757206698821241638313331) * 10 ^ 70 +
        2742703891254321580694428652781250938089183170948283869817643024701133) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_60 :
    recurrence5Scalar1First.coeff 60 =
      ((((2229525832623598279168132881495624982549856323582493141 * 10 ^ 70 +
        4103921614412717347684640074913995263208374314484032783750660262326741) * 10 ^ 70 +
        2890440218746845081735494890608537332511349136107258268006632696628937) * 10 ^ 70 +
        2163374680913148441983893859027604484871076213778218142388523964797390) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_61 :
    recurrence5Scalar1First.coeff 61 =
      -((((72401302914616814584638289211069257203549981196800458289 * 10 ^ 70 +
        1210270481333102545604622468072663748795882616746125654308470994440876) * 10 ^ 70 +
        1192661603843871486526929922273029089811828271616956096947402608493812) * 10 ^ 70 +
        7851009385691151077787312971839499798695065906863703651764690163986538) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_62 :
    recurrence5Scalar1First.coeff 62 =
      ((((2232359433284876797472254411190995216087530635197956503884 * 10 ^ 70 +
        9543952551680697892190227706263896249256058319890855500159172242049926) * 10 ^ 70 +
        1817372055768271435593790732924249506146623332469160870237557892249017) * 10 ^ 70 +
        8058437011702701222543547289293214344415678772402266982904446309517261) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_63 :
    recurrence5Scalar1First.coeff 63 =
      -((((65367723239231657312053021195719367167071203678938992968115 * 10 ^ 70 +
        9865701100752966076158857480419346047647156198997817082077606907089047) * 10 ^ 70 +
        6583567847499861953455985884305401083321945836671368789534797565934260) * 10 ^ 70 +
        2351126385734514151441175319281007788996469587473409524915363339667964) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_64 :
    recurrence5Scalar1First.coeff 64 =
      ((((1817799326125725383824811618438108211330172249240044371931954 * 10 ^ 70 +
        7492630902843086993131834942291361489136608401349435474128533963458817) * 10 ^ 70 +
        4758739757319761125303469487464380676045407095839065855253272605640402) * 10 ^ 70 +
        1692150773696784086301463409839703711609884676700109666539965938991036) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 65 = 0 +
    65 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_65 :
    recurrence5Scalar1First.coeff 65 =
      -((((47994727005570823614808889419992175913185159134506996237713268 * 10 ^ 70 +
        2332821892453178780077840747581956466536605437446791528511814363461022) * 10 ^ 70 +
        9414914342547397668130488332148037362822498640539522733667636195100306) * 10 ^ 70 +
        1349008878255591620079823309758141530977952265178524569905896982885514) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 66 = 0 +
    66 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_66 :
    recurrence5Scalar1First.coeff 66 =
      ((((1202346684032613812612017992886105832191499920225308106053971545 * 10 ^ 70 +
        1991037085185629013282367304856479070471606039576755298882983210365096) * 10 ^ 70 +
        2408527899217857950789472621145184092253416983948682703852835075439562) * 10 ^ 70 +
        9233241206083652322236135083134229718787325591819744446646310562204866) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 67 = 0 +
    67 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_67 :
    recurrence5Scalar1First.coeff 67 =
      -((((28546975877902474015403794780264331616632035352913210267463290119 * 10 ^ 70 +
        4933900752962323689093626354644097343012285000241585465987439692506671) * 10 ^ 70 +
        4840092304540312811424498683349791661053803530663016239741866563463468) * 10 ^ 70 +
        9989228432803381793920847317740359910129627854686746219902058455845359) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 68 = 0 +
    68 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_68 :
    recurrence5Scalar1First.coeff 68 =
      ((((641172093431329642010280548550149209739991296455078892156534964859 * 10 ^ 70 +
        9667439111599967592477078317918676542151607755752296179363081626368673) * 10 ^ 70 +
        5967379306828319658036656672668723006258181993505701693617546449046501) * 10 ^ 70 +
        6136056637119606732637901902490555924680803344693190068477140534611565) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 69 = 0 +
    69 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_69 :
    recurrence5Scalar1First.coeff 69 =
      -((((13582519003958717349947438621061814705937024082407303679038085852559 * 10 ^ 70 +
        8584352845403244682426373388772675952932386892231946432317430699463357) * 10 ^ 70 +
        0361483022900484325371755908645912293022094432784950976996344595465102) * 10 ^ 70 +
        8173362771550386210155862164183698545768252085029640922619526480949561) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 70 = 0 +
    70 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_70 :
    recurrence5Scalar1First.coeff 70 =
      ((((270083388781567260293418524490073403917470660881069091600300627078432 * 10 ^ 70 +
        6183313859027979145180734052165741845565108963333375166789553374474382) * 10 ^ 70 +
        9024646506347039757821623956325506811414460427121620295135132521082948) * 10 ^ 70 +
        9825904993025132610131534610286199531603447594392503929987034472794304) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 71 = 0 +
    71 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_71 :
    recurrence5Scalar1First.coeff 71 =
      -((((5001061876458114550973717099901305171651973286262037872561531050486210 * 10 ^ 70 +
        9913009993164588498080591111128385309484197916693530396165982340414982) * 10 ^ 70 +
        4011768606492464866195419849688075387593197214592203497399909430014536) * 10 ^ 70 +
        1647997847140593874956880299523017134092978218004414432608758281170319) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 72 = 0 +
    72 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_72 :
    recurrence5Scalar1First.coeff 72 =
      (((((8 * 10 ^ 70 +
        5015787267829037939007831141530297424457633932885889118962059828572526) * 10 ^ 70 +
        0774226966206287611553937913326860011021856348560222933722961701640976) * 10 ^ 70 +
        5077429326586345474167325470725027163764893029688259238488965980878592) * 10 ^ 70 +
        7468691488692137300024318503756846568589070474225875559170421506874355) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 73 = 0 +
    73 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_73 :
    recurrence5Scalar1First.coeff 73 =
      -(((((128 * 10 ^ 70 +
        9700970858390940532775642681004157690120052988854948599232522219855083) * 10 ^ 70 +
        3772028360984868497294145910570147107185450807572144516924310698706179) * 10 ^ 70 +
        7012275696510992896251218943370353180270655784504304195419679900934290) * 10 ^ 70 +
        7992013239361441141109863343619406511978560574618949836621925144924958) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 74 = 0 +
    74 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_74 :
    recurrence5Scalar1First.coeff 74 =
      (((((1629 * 10 ^ 70 +
        1012431649903183848326729135895642294557084960359002624044351346589596) * 10 ^ 70 +
        7537735253581702555629611574087138007449472912814302964940012191242572) * 10 ^ 70 +
        0299348981204128831533292539475782936496245173009873622656638810583783) * 10 ^ 70 +
        0744639354057034836477165343689334898729208715840709637942163821947307) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 75 = 0 +
    75 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_75 :
    recurrence5Scalar1First.coeff 75 =
      -(((((13153 * 10 ^ 70 +
        7013829330319526059551065556208426178642935130136360354718434899422199) * 10 ^ 70 +
        0146646208274437866943905831467065266194799959835517627631180089971002) * 10 ^ 70 +
        6290598714395628225366340961393284571451115014388723573985231225981294) * 10 ^ 70 +
        8364803289037983487064350901573928528891274051203096094478699591341247) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 76 = 0 +
    76 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_76 :
    recurrence5Scalar1First.coeff 76 =
      -(((((92383 * 10 ^ 70 +
        6948783906288068509430377521101629154101327149649171612752234512549887) * 10 ^ 70 +
        8041451665616686470128601669576910188051242491474351618353539626675063) * 10 ^ 70 +
        8488720028059089339570454374735718249214111050577977369719845067600765) * 10 ^ 70 +
        0352093830993729546923035191147339498490407089721051024965966395825977) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 77 = 0 +
    77 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_77 :
    recurrence5Scalar1First.coeff 77 =
      (((((7638815 * 10 ^ 70 +
        2786351189805005819075125479246109544447026910288053106908739667672687) * 10 ^ 70 +
        0308980552076407930908607704505618476910104172984438651230534876717633) * 10 ^ 70 +
        1522007936016307940136250625891681304980549539682073033975621501454561) * 10 ^ 70 +
        3867082295111710983649822713394150742821220538439072308194273131147674) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 78 = 0 +
    78 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_78 :
    recurrence5Scalar1First.coeff 78 =
      -(((((234465363 * 10 ^ 70 +
        1949052800375357990739933816305439726793742404626373699845304101618417) * 10 ^ 70 +
        3719587271669828420659384551060285467716622602067400254229324897311947) * 10 ^ 70 +
        0683415846412448872157755959033953591683485073230547848805947370505093) * 10 ^ 70 +
        3309487082347093529359420774845904781038731739061309259771014707025822) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 79 = 0 +
    79 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_79 :
    recurrence5Scalar1First.coeff 79 =
      (((((5602049545 * 10 ^ 70 +
        6735034132617841032382871073684697843025337908924411062009009797968910) * 10 ^ 70 +
        9832995915582297797064342738961696862232697923957470337649840449138943) * 10 ^ 70 +
        0417514483552597387003606725507821333373876086268639365338394794122510) * 10 ^ 70 +
        3433339192607899403353930966381287722405097373047747313459150558341803) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 80 = 0 +
    80 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_80 :
    recurrence5Scalar1First.coeff 80 =
      -(((((117158310561 * 10 ^ 70 +
        0161511051582500655057785344415632944755567774255211372708733965979969) * 10 ^ 70 +
        5984985882631891011251967774611227706867266572472131096809933493898905) * 10 ^ 70 +
        9848813257036018730269475106982662670869857513355396038124887666516838) * 10 ^ 70 +
        2070228229125158757424855627164997441098769058738505628369795130455304) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 81 = 0 +
    81 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_81 :
    recurrence5Scalar1First.coeff 81 =
      (((((2236806946204 * 10 ^ 70 +
        8166751291371872517062182517576243069688973915169256603265271895666372) * 10 ^ 70 +
        8717716779041513647785344933372358211879872364665052574934425733203062) * 10 ^ 70 +
        5503822397995659338941961728684607043084508023906991424914802941681583) * 10 ^ 70 +
        4843223135461124885234227175471720962859789949573147599790330934384490) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 82 = 0 +
    82 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_82 :
    recurrence5Scalar1First.coeff 82 =
      -(((((39779257671948 * 10 ^ 70 +
        6603833901328464658265418427264067401598909618678538711079894177618527) * 10 ^ 70 +
        4857971394038863006624816833659140055039322791851784275745084513639598) * 10 ^ 70 +
        2050045130038080188617137144336478984919647213290027939734906406300662) * 10 ^ 70 +
        6777602902257077828505155963932186668804148318732033615916828306791344) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 83 = 0 +
    83 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_83 :
    recurrence5Scalar1First.coeff 83 =
      (((((666462738494522 * 10 ^ 70 +
        1904634963207773404772480059684745947336787897137547285919020066909912) * 10 ^ 70 +
        6980439593897407438203603058770905621366114517296375993619396410630837) * 10 ^ 70 +
        3944984293803118239415013702183134080799092904535433905002395907587693) * 10 ^ 70 +
        2901819508561465481549512123260422127876805552937617233434209244860042) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 84 = 0 +
    84 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_84 :
    recurrence5Scalar1First.coeff 84 =
      -(((((10594101287520869 * 10 ^ 70 +
        8234105681354761273755489407009585150186540895198850965640351631392344) * 10 ^ 70 +
        6267633119775103284903784043186719410896460807900373385169857093633793) * 10 ^ 70 +
        6025116355416575005915913467689233417332256363509492475897279380514637) * 10 ^ 70 +
        3934760923499661202501844383336011710534423185634869504503969742734684) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 85 = 0 +
    85 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_85 :
    recurrence5Scalar1First.coeff 85 =
      (((((160546977967259997 * 10 ^ 70 +
        6745425524529986568495728962669390934997430517747265267741996301273290) * 10 ^ 70 +
        4670692076240887502049815636217009097104305536389318402577481847730854) * 10 ^ 70 +
        1867117023756026450244861058271464832235859965643158744153761803659172) * 10 ^ 70 +
        4534113174383363405421333503583043217602385674757527315127642482587463) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 86 = 0 +
    86 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_86 :
    recurrence5Scalar1First.coeff 86 =
      -(((((2327458653677306257 * 10 ^ 70 +
        5647081406421369318863398803895531497115452687490617494511939899630174) * 10 ^ 70 +
        5666762163168216099833563915834004763854199690952870209876174895225917) * 10 ^ 70 +
        5348885027242025657850720591301111559820375573446310170258689955658220) * 10 ^ 70 +
        4931453801632225662005533426881856579248611067067630637305442381577609) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 87 = 0 +
    87 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_87 :
    recurrence5Scalar1First.coeff 87 =
      (((((32361230050788637101 * 10 ^ 70 +
        1050800798333209378641065836471154231418550634375767008626405296322920) * 10 ^ 70 +
        9703918679256560270556691623960764498983840933891343224326025913767976) * 10 ^ 70 +
        2973562658803062982144510833786230734270923045915930271134642966894330) * 10 ^ 70 +
        2900444035716100662940116927201277485901285695856193013036631373345646) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 88 = 0 +
    88 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_88 :
    recurrence5Scalar1First.coeff 88 =
      -(((((432421245795615160105 * 10 ^ 70 +
        9445649922969941226968405526069533528095701175022310076684181718740007) * 10 ^ 70 +
        8438939836193223603764755904951989021794682018591285706519643739160672) * 10 ^ 70 +
        2178952854236262781119012063701125669089751547766286502688826275680595) * 10 ^ 70 +
        5912244773935179386228899914498138180468312139601302742628616083596781) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 89 = 0 +
    89 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_89 :
    recurrence5Scalar1First.coeff 89 =
      (((((5562039496672553300876 * 10 ^ 70 +
        5458911571772882756979718728414816939033481344977934250853925094322173) * 10 ^ 70 +
        4781141696131404242568100490408133885231712213176488624904605960610635) * 10 ^ 70 +
        7714991588992479449783808821546135201941749255239663311908877971083043) * 10 ^ 70 +
        0854416859311898392823422860360841885121168469509383005159399475175759) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 90 = 0 +
    90 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_90 :
    recurrence5Scalar1First.coeff 90 =
      -(((((68958994930255590685098 * 10 ^ 70 +
        1971324393957959280732827140031714565603178428439987363276471444925442) * 10 ^ 70 +
        0760449455894621155127258712400949688676519937742550570176369400069299) * 10 ^ 70 +
        9948345525367859390735592003416876834202591807785898267627010036378923) * 10 ^ 70 +
        9359652099969234630001663563536855090035843928512671776933150586704057) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 91 = 0 +
    91 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_91 :
    recurrence5Scalar1First.coeff 91 =
      (((((825036222712578862141701 * 10 ^ 70 +
        7594811581215465114185715361446299752869113571229675949500370013833879) * 10 ^ 70 +
        2735057185551663014195633072393226412107777149703267731654097107465119) * 10 ^ 70 +
        5803655012178709581982663403118706173679393206754197962885663083176649) * 10 ^ 70 +
        2082598336426552144032261504870108666490769278201653916195405913108068) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 92 = 0 +
    92 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_92 :
    recurrence5Scalar1First.coeff 92 =
      -(((((9534727625667439658403321 * 10 ^ 70 +
        7631863004948700271336266113636944387983965395543273003741478165900160) * 10 ^ 70 +
        0499026930368389444937765340358131359584150199530764738251886845419589) * 10 ^ 70 +
        8777308957204089954242081419006097655362576163704543096951401166066790) * 10 ^ 70 +
        7662790284357354727326172593147951316071404157090077517002802527238878) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 93 = 0 +
    93 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_93 :
    recurrence5Scalar1First.coeff 93 =
      (((((106530154851587731772984146 * 10 ^ 70 +
        3348785926738573393180687400356224430165150347726893407573326033364416) * 10 ^ 70 +
        9704896567570691051205653433558870290649811337127948223143893476157329) * 10 ^ 70 +
        7548248738989905755673191335789027640876951382221037909714096605511084) * 10 ^ 70 +
        7946108373906006169341710984046145554352583185383568965239289672222461) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 94 = 0 +
    94 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_94 :
    recurrence5Scalar1First.coeff 94 =
      -(((((1151597063383116154988377033 * 10 ^ 70 +
        2249471155148171359785373909502602261043299265312087306112584343510657) * 10 ^ 70 +
        6918717660911505697459790680826958032696663801376277762816595754119305) * 10 ^ 70 +
        5167486448170141293594501014588368950636719334612309719780554914252507) * 10 ^ 70 +
        1516787126173697912444584622584784327519959446983624906674023549921114) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 95 = 0 +
    95 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_95 :
    recurrence5Scalar1First.coeff 95 =
      (((((12052969035774863452719111297 * 10 ^ 70 +
        2609894765653034834097037863598013536361923939632031902751132777324562) * 10 ^ 70 +
        8890435493149699403246960539908185055491762813238277429970262079683910) * 10 ^ 70 +
        5362445094048429303942634071769278252362280955856326814128846324118930) * 10 ^ 70 +
        2977659088165578820870289650856140195849120192523697484396763327815790) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 96 = 0 +
    96 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_96 :
    recurrence5Scalar1First.coeff 96 =
      -(((((122215967027882186941774454025 * 10 ^ 70 +
        0368187670163100254349086273164973636482380245156603234148410688126498) * 10 ^ 70 +
        7526897666398530006810201094029348614409701836791047779243398443423474) * 10 ^ 70 +
        3499411795033571866997377362791433750141761381088871070992166544758917) * 10 ^ 70 +
        7905122563553490779931703980560105384048043956737363574671602283734439) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 97 = 0 +
    97 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_97 :
    recurrence5Scalar1First.coeff 97 =
      (((((1201309632089800252921907711259 * 10 ^ 70 +
        9799688446787751285519019257375415504798771698576323497666564895353347) * 10 ^ 70 +
        3881925676288096670869833539397252208988118721376801689965207452982607) * 10 ^ 70 +
        1036362624785702404727243520485216675270884605670994732876522515430063) * 10 ^ 70 +
        3599620376807226023327553953550352302751063445647345860498590121924846) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 98 = 0 +
    98 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_98 :
    recurrence5Scalar1First.coeff 98 =
      -(((((11452732638774247856375891262859 * 10 ^ 70 +
        1500105032673028980100292609172482898771405328566605733650373040251742) * 10 ^ 70 +
        3016630742280044226859028718365583985994338778719910802974508721993209) * 10 ^ 70 +
        4718454010192532982507165594811427376019417107265075567137661718145628) * 10 ^ 70 +
        9581702661310177295649424014300908101126799274760521646003711505210553) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 99 = 0 +
    99 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_99 :
    recurrence5Scalar1First.coeff 99 =
      (((((105951878428630256461685441181790 * 10 ^ 70 +
        0911633330853517740073277086027759201051846379133028521923625048090606) * 10 ^ 70 +
        7741074340474901487158933654675501444391835475606618142770808493372547) * 10 ^ 70 +
        3356496440508454014135333491772475293571610943400281797677063547646521) * 10 ^ 70 +
        8428278406858655230609165146635130449532950390528228238254589376201444) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 100 = 0 +
    100 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_100 :
    recurrence5Scalar1First.coeff 100 =
      -(((((951608262621805603758224713273813 * 10 ^ 70 +
        0641020992366022325535760911282856841007807576513122833309288007859358) * 10 ^ 70 +
        6385510110172937637825587297018961998691798420037071404383660427421491) * 10 ^ 70 +
        6986516265789120955512819083103907829087091263811031989275698748724449) * 10 ^ 70 +
        1349795837499490798961289430241121947417184920868008208793598328416233) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 101 = 0 +
    101 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_101 :
    recurrence5Scalar1First.coeff 101 =
      (((((8301385498636232353637966731861065 * 10 ^ 70 +
        6139814025316749680466925772421647035010086289993336960313251654824568) * 10 ^ 70 +
        7250560124457119155817667401407746311099773606580031150882616318375904) * 10 ^ 70 +
        4993244515166374658489633659851375016448415681837604118034223783112326) * 10 ^ 70 +
        1295805438168735101174619933658516925735306216621503903189853106800845) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 102 = 0 +
    102 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_102 :
    recurrence5Scalar1First.coeff 102 =
      -(((((70366877043547421122758499930878220 * 10 ^ 70 +
        0147363237788208422814174238061840757838615435950759077981564239361493) * 10 ^ 70 +
        7625214789759347904518746312139401134696300622989575762472150845913845) * 10 ^ 70 +
        2692845405732077413801811290267129760773211271304502793674263795177940) * 10 ^ 70 +
        6167033130732500256884382765541908293578625208270026099958781646033484) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 103 = 0 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_103 :
    recurrence5Scalar1First.coeff 103 =
      (((((579808552897902278080893326830837799 * 10 ^ 70 +
        9816641755665247177619537392140206173447611426587909362348681238565113) * 10 ^ 70 +
        6087337708553945076554680266304953621167869976631225532031900994962150) * 10 ^ 70 +
        3844185898104137783006651493862029511334129440667401222106594969910665) * 10 ^ 70 +
        8380813277630235398042300600277956103262775003995630540818998076438103) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 104 = 0 +
    104 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_104 :
    recurrence5Scalar1First.coeff 104 =
      -(((((4645845487674754288217290576043113037 * 10 ^ 70 +
        9704652330077808059881774071519104133220235021505514262402731732221673) * 10 ^ 70 +
        4980241233971198106596594523571015606127855078132987433119726255173812) * 10 ^ 70 +
        2395688141635553267297199942427283502289936990658984510573837654888123) * 10 ^ 70 +
        4098332791547603199539249666017390758776841491438983818475530228840922) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 105 = 0 +
    105 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_105 :
    recurrence5Scalar1First.coeff 105 =
      (((((36213168042294322081411605141969448954 * 10 ^ 70 +
        7405433373241210823825550171603013310596155453586339521148711362037370) * 10 ^ 70 +
        5437707056309855748371530484410225487080200876454796006319967817043201) * 10 ^ 70 +
        6784151638558074308780633209649589673238842446611808714293443295696466) * 10 ^ 70 +
        7888617706571816250233637017893751168867272347241070628705228753295802) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 106 = 0 +
    106 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_106 :
    recurrence5Scalar1First.coeff 106 =
      -(((((274688857003236296034434075786147248678 * 10 ^ 70 +
        6421008113664014831050525689726976633566675279367336562117713808999650) * 10 ^ 70 +
        8759843446007793278669374248178692387023769914825115323251404965521838) * 10 ^ 70 +
        7539966974986310189142573084779829704634478468036209294175147348433526) * 10 ^ 70 +
        2513973023955445738016469180200127039719155347696973997352783101006681) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 107 = 0 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_107 :
    recurrence5Scalar1First.coeff 107 =
      (((((2028305666697557796404335220463698937388 * 10 ^ 70 +
        2237605726386591920418264841592525882303363864554334322315297663623099) * 10 ^ 70 +
        2192809750007376371273241648236698212191801244555405855067852290244339) * 10 ^ 70 +
        0509254396352963826960627905955822085139985771132177043866842565375549) * 10 ^ 70 +
        6739404925581462131472080468991063940799463822048491192403737990199218) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 108 = 0 +
    108 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_108 :
    recurrence5Scalar1First.coeff 108 =
      -(((((14584216493461797879758747406505943209151 * 10 ^ 70 +
        5500999627127828196455892182603660537003666289798873496213106967049306) * 10 ^ 70 +
        2241752159100252457520632980954566793971280261323623359347680106204241) * 10 ^ 70 +
        6339322583514555706036806333716071951867883589115757591345102141604515) * 10 ^ 70 +
        0706402127906689982222760803741809170069233483549775247326963181687470) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 109 = 0 +
    109 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_109 :
    recurrence5Scalar1First.coeff 109 =
      (((((102146733725015838078140903435184078690271 * 10 ^ 70 +
        6623096155357547519355745067870994344770367985287743203040149740408454) * 10 ^ 70 +
        2431340790872984333115332406660734315125515130969267799288677146204830) * 10 ^ 70 +
        7207825615437590229475608059507555773324462658100251339836069525215303) * 10 ^ 70 +
        1779680978787020623487665255364489880048272557687183985844758046735593) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 110 = 0 +
    110 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_110 :
    recurrence5Scalar1First.coeff 110 =
      -(((((697087206399508817744541189554905691067727 * 10 ^ 70 +
        1323097612951370072832442000729148056641671021281316783423715152716805) * 10 ^ 70 +
        4069917171976352593259122942349380539700630269996639477187228942816913) * 10 ^ 70 +
        9160744285845647396358310061685622519599026064698549942264780272222612) * 10 ^ 70 +
        6834656786907189496086833282593497437045146279114309336772670218998588) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 111 = 0 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_111 :
    recurrence5Scalar1First.coeff 111 =
      (((((4636562176893013538586791782794639440068576 * 10 ^ 70 +
        6384639744173941716135397226242011633287466559831054380824996182567343) * 10 ^ 70 +
        7797367224183122943327925997305726818411627346097075805660145243947409) * 10 ^ 70 +
        5238901710198809175423352096104595180920076602069394263818821068782972) * 10 ^ 70 +
        5189450959544589816466363569103243420301439891544674262243538499066981) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 112 = 0 +
    112 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_112 :
    recurrence5Scalar1First.coeff 112 =
      -(((((30065769929895447354802406290185068138295989 * 10 ^ 70 +
        5111381866059359015458302009801319537139814637910440784584348190134770) * 10 ^ 70 +
        8352955033931345596884323748651079928135891255216328824411318571724439) * 10 ^ 70 +
        7407858215727923567659592437150246845740326243766752860639348978821006) * 10 ^ 70 +
        0013301238919308518876361387811467187855945579580251332614449602356528) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 113 = 0 +
    113 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_113 :
    recurrence5Scalar1First.coeff 113 =
      (((((190122194384391995269570896884219485953857444 * 10 ^ 70 +
        6391495728532356258041172277929338963979312532470254361626064436631547) * 10 ^ 70 +
        0759615709208081082078010210345849304931889160042910306475991461460852) * 10 ^ 70 +
        6334347519299714983113225515037186339904855451772179544015225295459061) * 10 ^ 70 +
        6706221142941258367435556199897798900958526726831032929393734707846460) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 114 = 0 +
    114 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_114 :
    recurrence5Scalar1First.coeff 114 =
      -(((((1172710501229437969752828936836529087758300364 * 10 ^ 70 +
        0399724634760073343590146570809353034533346387260846037938218814378477) * 10 ^ 70 +
        6875308524053040916528051955115986647086485971363597381979068112356338) * 10 ^ 70 +
        9917605742017514489913853695746460673806194947209933050258245899681128) * 10 ^ 70 +
        9488453731023618701096608080106399612671206833919771457912674885451643) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 115 = 0 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_115 :
    recurrence5Scalar1First.coeff 115 =
      (((((7057583916110527786534305181794824121884581678 * 10 ^ 70 +
        9260790700136261592463551984379467679674991524852531921752564864187716) * 10 ^ 70 +
        3121794314720968508328581657334015653400788249474982281166161277467594) * 10 ^ 70 +
        1516150334454539529512095360451653835361968578598194214938952218420595) * 10 ^ 70 +
        9730417919466846896337395711372118983958326176755897417959985425153793) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 116 = 0 +
    116 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_116 :
    recurrence5Scalar1First.coeff 116 =
      -(((((41450989853065871059496914668705574712587783792 * 10 ^ 70 +
        6007577902806659845140556784350181081899382922743340033093885757595517) * 10 ^ 70 +
        0380352531265626759986945262989851788639349851391466417512972221069925) * 10 ^ 70 +
        1718388485468395851719340883801028489064795305816901852017206428976086) * 10 ^ 70 +
        6872781338839160664932159064620244284690716338330480659140763750508282) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 117 = 0 +
    117 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_117 :
    recurrence5Scalar1First.coeff 117 =
      (((((237646026576916323142159305505773476485835224571 * 10 ^ 70 +
        8613691266137006802961787565702766496399889845046602245129715956636385) * 10 ^ 70 +
        9223431058271011831796230287694702491809473113888889135181633887118307) * 10 ^ 70 +
        6098612151814847845257159417051244335946046101446811853401263788283560) * 10 ^ 70 +
        5108930756229859381856424183990683105863129095381284164641651217975088) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 118 = 0 +
    118 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_118 :
    recurrence5Scalar1First.coeff 118 =
      -(((((1330280180370450205150764660376989934139820117975 * 10 ^ 70 +
        0082236062389431965503685812274531019508543164172889478894561477169899) * 10 ^ 70 +
        3872703163741254815105304395731832102826810628585372896390737096849139) * 10 ^ 70 +
        9291790205629669455779030033417565844915691376372973447273466624582268) * 10 ^ 70 +
        6552515872149168545656321479550771555726148660294220119615614793658245) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 119 = 0 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_119 :
    recurrence5Scalar1First.coeff 119 =
      (((((7272266355494638331037925983937536637222976521770 * 10 ^ 70 +
        0798598154457130698263694376921001515561770012990320353849997399108717) * 10 ^ 70 +
        7330904451208774527801556154035706854835195427406181608727263298669552) * 10 ^ 70 +
        3831394700254136506591377572116634855893146146936002292960179312327626) * 10 ^ 70 +
        7026916716536892503032170663408285116714901250532434533773983984284518) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 120 = 0 +
    120 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_120 :
    recurrence5Scalar1First.coeff 120 =
      -(((((38833352768780641988552009877088242496733102179117 * 10 ^ 70 +
        3594607779037697614562105462954184417121915460067778645483163673064375) * 10 ^ 70 +
        4903904115708125613771829567897361225166303762421254434920130480743999) * 10 ^ 70 +
        7319381218514945093692192210475492515979347346980287583681146905441155) * 10 ^ 70 +
        8312770343661261425395944944724506485654940398882977339314475151557020) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 121 = 0 +
    121 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_121 :
    recurrence5Scalar1First.coeff 121 =
      (((((202600307778675469327256794123751652252418494501117 * 10 ^ 70 +
        5649569134888802155265165255230218937933578814425733047137191929865742) * 10 ^ 70 +
        2026187660788669682069787065570511476973236655041090534561728925911744) * 10 ^ 70 +
        9275826715701668377423592451924393225682770449479792932328909589572267) * 10 ^ 70 +
        0906389266401998449660522559469793983125311591957350440647025437625660) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 122 = 0 +
    122 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_122 :
    recurrence5Scalar1First.coeff 122 =
      -(((((1032914670540623043165963127081155624524320071923266 * 10 ^ 70 +
        3435283690616223900553250748634925401765185893526011699776735393205308) * 10 ^ 70 +
        0959649152457199628686781689878335775424683215706116407375716316147056) * 10 ^ 70 +
        7904445884223871714193498858710721551908466390239923299843214508661309) * 10 ^ 70 +
        9721794821195415530052073087629932184635202256554791853826277629201401) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 123 = 0 +
    123 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_123 :
    recurrence5Scalar1First.coeff 123 =
      (((((5147121573453632676401979455320828276077854748277307 * 10 ^ 70 +
        9710458802733872548686133111328131204418942276900135101712729843789308) * 10 ^ 70 +
        1630214470815379354157425514587670317110577416392032010633075153012011) * 10 ^ 70 +
        9857938406559710216476171610049727544756587747285211405966346880101179) * 10 ^ 70 +
        4738313247510499665409547849476976300401813889387622300951530585406946) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 124 = 0 +
    124 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_124 :
    recurrence5Scalar1First.coeff 124 =
      -(((((25074027740475403672535174177473867710587967198418653 * 10 ^ 70 +
        7070988426158636875174339159847431437298838308187728949782309445286628) * 10 ^ 70 +
        8861220847722989791837672019799538741576080308218292220558199414297799) * 10 ^ 70 +
        9147187687703956469551615644351215341513511006393214513790533459293837) * 10 ^ 70 +
        3830258892881906997960175181688373447085033840027252786206681001042205) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 125 = 0 +
    125 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_125 :
    recurrence5Scalar1First.coeff 125 =
      (((((119433227086100633611920922243482802698455394320532468 * 10 ^ 70 +
        6101567243181590107344407625541643674558424904343648982356369646908614) * 10 ^ 70 +
        1322995614392786935866857719370487123861071557324867616129579667448688) * 10 ^ 70 +
        4070767205315009449701700294239185982460620590218788452125154392290019) * 10 ^ 70 +
        3378642794897760615163645267526268881563779774266990220685090518434848) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 126 = 0 +
    126 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_126 :
    recurrence5Scalar1First.coeff 126 =
      -(((((556348630350420261706776755529187260376743096750650301 * 10 ^ 70 +
        2565617552240666366909771961103504694679591945260117255703130015564754) * 10 ^ 70 +
        3607910443789886135740124071428488936690583921180589737878527061155887) * 10 ^ 70 +
        1457134230723106746019657007571862263526435214089882322411740635871789) * 10 ^ 70 +
        5590811631687521830587217941649098973486444006052754636083480702390515) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 127 = 0 +
    127 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_127 :
    recurrence5Scalar1First.coeff 127 =
      (((((2534935120339289174005942527583964520810317399941687057 * 10 ^ 70 +
        0058399921522799968719763744069752361999960293078715859732533621396627) * 10 ^ 70 +
        1342192916159879662540031017476547980599446924424056350744486647228733) * 10 ^ 70 +
        8318891424292054831898353624903680705523277393796719435905394543661594) * 10 ^ 70 +
        4626033326062164077620739149967947506344035888322760047766546503743305) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 128 = 0 +
    128 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_128 :
    recurrence5Scalar1First.coeff 128 =
      -(((((11299511334431334885610366591083266756112185096846096875 * 10 ^ 70 +
        3355445716771878547906130781030824112070826419949132726161438042846603) * 10 ^ 70 +
        6917249294531487932876150789446493566615194544358134082182340092984794) * 10 ^ 70 +
        3666704819539060752781340219659107277477015874262306624049628796334086) * 10 ^ 70 +
        7368907852360391706044616949657716896171808658595853022518271102517394) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 129 = 0 +
    129 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_129 :
    recurrence5Scalar1First.coeff 129 =
      (((((49283141899030274266274330776448027758182741001463373310 * 10 ^ 70 +
        6009917629767267957082825982555262607243905662351842938892677288460399) * 10 ^ 70 +
        9884151949006916004195958833186689379203223751130938707970594488831282) * 10 ^ 70 +
        9952913135830107596179144824134180354981251594088713018868562420192814) * 10 ^ 70 +
        9857588164006891127385813110298894458148447125908140053101290235900206) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 130 = 0 +
    130 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_130 :
    recurrence5Scalar1First.coeff 130 =
      -(((((210355517785035782244264026003454146002256892908996318675 * 10 ^ 70 +
        8447691937371878683035207969466362887316199076165812612255700451597981) * 10 ^ 70 +
        3071143385134208343416207375025381773526847165521766947501769009283931) * 10 ^ 70 +
        6195382849281769255781784893931912664032129681471108975937457863420255) * 10 ^ 70 +
        6813237893844659676482087985848499922118098605939289711845454255745698) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 131 = 0 +
    131 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_131 :
    recurrence5Scalar1First.coeff 131 =
      (((((878810280552032589748062025162386420602631693821297127656 * 10 ^ 70 +
        5918762436028241745954861413978041819632574385633449008287241474448487) * 10 ^ 70 +
        6782345720868034217996502772981272105349566350899393847978385912984737) * 10 ^ 70 +
        0615606770604162612767309264914735933152777151248266684156547105290966) * 10 ^ 70 +
        9362676996443878499681355781282396873753625581591187129873590294869239) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 132 = 0 +
    132 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_132 :
    recurrence5Scalar1First.coeff 132 =
      -(((((3594090623512783949016618684460191011211534567456169747137 * 10 ^ 70 +
        5407436173919717294513974151911168810927827811095998977238077440687169) * 10 ^ 70 +
        2837816875138732735527752927656797583577389767837064070686483707898525) * 10 ^ 70 +
        6052079920356888782723583411752394202234425618200234065093953255893348) * 10 ^ 70 +
        2745145624901222743814259573453799216836880458802207847191393392684515) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 133 = 0 +
    133 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_133 :
    recurrence5Scalar1First.coeff 133 =
      (((((14391322027640971674443932815613320540288087267329169236388 * 10 ^ 70 +
        8751910238116076854568480641750561986526863270511365824558111382541995) * 10 ^ 70 +
        0286430529305587427175889165870721930430476329335371151117057367868258) * 10 ^ 70 +
        4243828179084966120491070437846960227120920992669242645836340919359488) * 10 ^ 70 +
        6959236845679640216236273016730110185957752436893509100023272863833552) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 134 = 0 +
    134 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_134 :
    recurrence5Scalar1First.coeff 134 =
      -(((((56427837171089268135357514825796118298678536154519181703650 * 10 ^ 70 +
        4384986305295581680903163138457513925015485918097129061602203890136580) * 10 ^ 70 +
        1404699264245863980976303020428350620229603543115527397387105931909410) * 10 ^ 70 +
        4927471744703523257007853659833026141074136126925931883523664518873188) * 10 ^ 70 +
        0308129073602122595306909097380268132185438311790775372380394316724064) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 135 = 0 +
    135 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_135 :
    recurrence5Scalar1First.coeff 135 =
      (((((216684904283555666355927941591951445737861885798761046333313 * 10 ^ 70 +
        1583137158842492033196855413330163040056309696303189208102297781064528) * 10 ^ 70 +
        7219735576507939224583369972236139596264830270702459114688882161487393) * 10 ^ 70 +
        8847303274160571555928380307268077213910224873880145640807926166798936) * 10 ^ 70 +
        7465196568707853351029039765149322562591616408616759007095746970629077) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 136 = 0 +
    136 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_136 :
    recurrence5Scalar1First.coeff 136 =
      -(((((815016138533989617020939651952553393655645141293832068161579 * 10 ^ 70 +
        4246604725955702853934528557285949438124682635834440938319011409770050) * 10 ^ 70 +
        8723932106567127363286049307266393430939349402416128819290993794096370) * 10 ^ 70 +
        3373019212538159624046833310510615021894687624608203644599117886735289) * 10 ^ 70 +
        6219195334043228866883095726940923910964822348702890569301756798607750) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 137 = 0 +
    137 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_137 :
    recurrence5Scalar1First.coeff 137 =
      (((((3003060859467761171745545091066170546261557987870707380141789 * 10 ^ 70 +
        5392096043412303923135904248465395276249328869593469445830116143454661) * 10 ^ 70 +
        0317569024676141115350671137628788575821163517973770848772187093972568) * 10 ^ 70 +
        6189581558973236845971592461568478366511477830873267789044736186395385) * 10 ^ 70 +
        1507534816067693755375274703971213727371570797412365895388606216212479) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 138 = 0 +
    138 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_138 :
    recurrence5Scalar1First.coeff 138 =
      -(((((10841237543220153331177212837649916429368643188484464971055359 * 10 ^ 70 +
        3791802504210206168026388913337060935050806206389598692868028280008241) * 10 ^ 70 +
        6915545465251867357443723116931934201666275466359232848643230166452586) * 10 ^ 70 +
        9428365766129909327355550885232956169124160963329326170263204999176353) * 10 ^ 70 +
        8494567364329824425151109747000960026526889073810064143440758661259312) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 139 = 0 +
    139 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_139 :
    recurrence5Scalar1First.coeff 139 =
      (((((38349986406900856653874143569470088989189471594971120432402359 * 10 ^ 70 +
        1496937861438187759546929053774135305860552340089545326565616294437979) * 10 ^ 70 +
        0276694390913580408356423273070616636752345243969453151520209290416444) * 10 ^ 70 +
        2204398575600363512463435217293752449572863034684057604798280931271789) * 10 ^ 70 +
        8425423560110079471972565690785687177521051622903467916842046252813544) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 140 = 0 +
    140 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_140 :
    recurrence5Scalar1First.coeff 140 =
      -(((((132946362243817375957154585389189973081926146191988121352328346 * 10 ^ 70 +
        8506849294606331938623074870497073921980123105753950852121515580665468) * 10 ^ 70 +
        3932917934727047442633687381643206593516705580137090400863609933690146) * 10 ^ 70 +
        1369758892962394425779549810375224589832371446778686269307593524587689) * 10 ^ 70 +
        8041099818222628227672339926855850021654583043553898598651675287454450) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 141 = 0 +
    141 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_141 :
    recurrence5Scalar1First.coeff 141 =
      (((((451714812241042993826361097133995220741534735638799430395531532 * 10 ^ 70 +
        3564575720086337045684415263940748054706498270441379957778947434417948) * 10 ^ 70 +
        4362053607783302926218402557906064249654659655511323119508820387482228) * 10 ^ 70 +
        0393052814340077048559717375746913827925963178042288478194307600601014) * 10 ^ 70 +
        5117216852453000677709031414209674775980691122475459250544032871799770) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 142 = 0 +
    142 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_142 :
    recurrence5Scalar1First.coeff 142 =
      -(((((1504454604146525562178884838822395686995908432680208810910800997 * 10 ^ 70 +
        7244953874985249270333845967157649342120990720012180679288082915313239) * 10 ^ 70 +
        4641083756872187032473544400765118996883591906306243428282730774189810) * 10 ^ 70 +
        0317218142800139383276772188794935061329205787644264094058224128939171) * 10 ^ 70 +
        7051303798519869008356428923186350368777702434022814242309870478364404) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 143 = 0 +
    143 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_143 :
    recurrence5Scalar1First.coeff 143 =
      (((((4912126355947265727227052190715825434778921327947272717142118242 * 10 ^ 70 +
        6003118512616539143926916107583841482248472077788897578442561431065940) * 10 ^ 70 +
        9986641124293743213499424665349772830473612126514124139241250609184619) * 10 ^ 70 +
        9507458978809446694046883404426633754574428515020330181228078378535296) * 10 ^ 70 +
        2638925250888744197883723978663147536699966593261116817326886822633217) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 144 = 0 +
    144 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_144 :
    recurrence5Scalar1First.coeff 144 =
      -(((((15724724549532022132916118370282504206606465001281149838490500949 * 10 ^ 70 +
        9235734227313404591046842955798986858010675440785888502071798609783988) * 10 ^ 70 +
        2941447737380837054059909060988579118038002054625434443746978194543611) * 10 ^ 70 +
        7052826292386165094626422523207487044706678634628096076699660616300498) * 10 ^ 70 +
        6813026819732933311358554462076932171189666868059955879140810878285537) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 145 = 0 +
    145 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_145 :
    recurrence5Scalar1First.coeff 145 =
      (((((49358919732904860515409223982825430244198768752348234817072510648 * 10 ^ 70 +
        9416114821156955324182564070693441519079644239488404820424907662508958) * 10 ^ 70 +
        3717790329704198494640667002498473854754469753311846745907291119235062) * 10 ^ 70 +
        2697709995695421134416902071657998764075079770683679383265209969789182) * 10 ^ 70 +
        9438676932054630266586828178962757582438671354350424090183827522136755) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 146 = 0 +
    146 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_146 :
    recurrence5Scalar1First.coeff 146 =
      -(((((151936454401947810303360538180126576250485528773057816210060737947 * 10 ^ 70 +
        8239537223361282706222594540083333651805080161315465878266449540562563) * 10 ^ 70 +
        2954081725155884651925733772826200640182383480399520252400290754982750) * 10 ^ 70 +
        1531255030339550301980574158518111394803028602664038475600891430847884) * 10 ^ 70 +
        7250080313320626800145033226299445852971567115507913973592686597793392) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 147 = 0 +
    147 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_147 :
    recurrence5Scalar1First.coeff 147 =
      (((((458685922923966332039459837280227300468105928229641690927506144761 * 10 ^ 70 +
        2758893882168937480980998837262048209904900484832139193339510342194993) * 10 ^ 70 +
        7642358177933522570114404615468251584958952284640191014746066466164383) * 10 ^ 70 +
        4278544391237327670359277684708137745829382688418890154790000056850072) * 10 ^ 70 +
        7986521232014373559577576712879558445263503142791569955301279718827483) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 148 = 0 +
    148 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_148 :
    recurrence5Scalar1First.coeff 148 =
      -(((((1358213279985123782293988889899015524796166128186789508106330047907 * 10 ^ 70 +
        9920647166040813155886873874893851497726101098748339535007912894439454) * 10 ^ 70 +
        8835998765488411365522394832385987299683328470617242193984347658452205) * 10 ^ 70 +
        7071227482799984102421636400472254739521276124994315551961621616246489) * 10 ^ 70 +
        6881947372259096494139657197861402065618749815503688166683591146029425) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 149 = 0 +
    149 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_149 :
    recurrence5Scalar1First.coeff 149 =
      (((((3945122223911126722469154221528570405415571891411343684936107429752 * 10 ^ 70 +
        4707197020759384086134420707553390219275105303143257374030001006361760) * 10 ^ 70 +
        0882590260505140816102279295036545359858248327552587894563195635252238) * 10 ^ 70 +
        3711433511802988876552609586618497597059132977907302402188921216405844) * 10 ^ 70 +
        0973491756454572609665208812574369845919602908000278139919926575102394) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 150 = 0 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_150 :
    recurrence5Scalar1First.coeff 150 =
      -(((((11241711672304266960859001917478791976447276246804799003486794960269 * 10 ^ 70 +
        0920598727371283054379036481867232374068138500204700387129001430842137) * 10 ^ 70 +
        2595744497680725502622609280651662498017283706793947214291881777548925) * 10 ^ 70 +
        3264282526552990816612450476404489228445418994500871163091959303681363) * 10 ^ 70 +
        1740974197383316418786029633044736936894311565668943388062424186100837) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 151 = 0 +
    151 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_151 :
    recurrence5Scalar1First.coeff 151 =
      (((((31428399391978415194701859269400283831051832698061624024504639523460 * 10 ^ 70 +
        9594765487688896633185562915865089191784389128671427931534109055421464) * 10 ^ 70 +
        6948412833925216832777343061188445729708493145697981126436756715983387) * 10 ^ 70 +
        2864017068446773374864840077864000079150164701814083878363048034361519) * 10 ^ 70 +
        1362964831477024270137589651083045904358133153351990617335701800319510) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 152 = 0 +
    152 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_152 :
    recurrence5Scalar1First.coeff 152 =
      -(((((86211875712058195236708033698078720711709825435534435164990643578424 * 10 ^ 70 +
        7573684821167201817385781408879135428945836113728538657389057163214562) * 10 ^ 70 +
        2917401906581775599400096607320459314584668936674485082369312155081509) * 10 ^ 70 +
        1433378501369985525109878930034776946848319052622574568451382851788094) * 10 ^ 70 +
        0600623478358372055871754352696169092138956570843617249813359699191325) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 153 = 0 +
    153 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence5Scalar1First_coeff_153 :
    recurrence5Scalar1First.coeff 153 =
      (((((232061417145670779178501984962002324828475171393337103867866122060866 * 10 ^ 70 +
        3964021670246917761298611232831517373714605619488432687017793348033747) * 10 ^ 70 +
        1033589094206774742723878031138729087411418122531846583803863039992073) * 10 ^ 70 +
        4852780736016009376572668997222798102628205917571845659785787693661512) * 10 ^ 70 +
        2598037317405649997419211126076895251189696484583230604403171705680843) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 154 = 0 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (154 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_154 :
    recurrence5Scalar1First.coeff 154 =
      -(((((613005915955283557561954133157781947827803601501690086586451618594614 * 10 ^ 70 +
        2334767098922771017958595080548725895471611632101573346402957620812055) * 10 ^ 70 +
        8723410780116562941647383909284841196075372541721770303076715840134440) * 10 ^ 70 +
        3918674237244398810682415938605076159068579038081269436360793244460046) * 10 ^ 70 +
        1935074159710019057235759907323495341612081195656649959147515613959661) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 155 = 0 +
    155 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (155 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_155 :
    recurrence5Scalar1First.coeff 155 =
      (((((1589227288153463517932631569137087387324646588844332456245365234274605 * 10 ^ 70 +
        6592502906936455492710305097287198506791500537263441223165170278310099) * 10 ^ 70 +
        4139405747764539205432520943745272889994548790066519240611892474853825) * 10 ^ 70 +
        4395831292134394738014430892355452880128776309810846624155766755577799) * 10 ^ 70 +
        7165323042872346921508923911871537685270376534813743444893305809583014) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 156 = 0 +
    156 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 26 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (156 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_156 :
    recurrence5Scalar1First.coeff 156 =
      -(((((4043892672570430983920187552402262574824847493427644682749209347770807 * 10 ^ 70 +
        6323529377943601516682107073288391900672616806595862452069354391443423) * 10 ^ 70 +
        5269474721420010280051424824926243683120724447189568582252273339958995) * 10 ^ 70 +
        6550242692539297577404742739774192076169989761890520854707722200004888) * 10 ^ 70 +
        2604106237212017680104235722702694489862776927358811478265052927383994) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 157 = 0 +
    157 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 26 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (157 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_157 :
    recurrence5Scalar1First.coeff 157 =
      ((((((1 * 10 ^ 70 +
        0100364217989582627168939552907650594830914299638370751643743762845758) * 10 ^ 70 +
        7788148923292200824233275411526183068955545053828772695568798652205886) * 10 ^ 70 +
        0104781632597241222747475201179647550314078107595723970728418711229375) * 10 ^ 70 +
        8685791829532528627144478324196133409410765199068164416114594275918449) * 10 ^ 70 +
        7398305789257237289579287955136813713697589027820483712550082759911696) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 158 = 0 +
    158 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 26 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (158 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_158 :
    recurrence5Scalar1First.coeff 158 =
      -((((((2 * 10 ^ 70 +
        4764452326510125592911003121420386535562480410225904065782750769267245) * 10 ^ 70 +
        2877161785379926735917723080008507483275436825038303590317440016988900) * 10 ^ 70 +
        2055402615084355882894407491130972593477821061703680785970316936158401) * 10 ^ 70 +
        7574709576977484336007234951759107031707487576023406932293545468778689) * 10 ^ 70 +
        1226544900099526429046741390696761393250240596115780307965145502959384) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 159 = 0 +
    159 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 26 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (159 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_159 :
    recurrence5Scalar1First.coeff 159 =
      ((((((5 * 10 ^ 70 +
        9607939367946331642192200163366066075376757434164556092373100499801419) * 10 ^ 70 +
        3477293959570038371084707455569157582972011096168082446433012649023714) * 10 ^ 70 +
        5665471156383416329828731086616865402021886300299364609483451010630502) * 10 ^ 70 +
        0009525501573388325237595632239987867008836229294378215314447814762257) * 10 ^ 70 +
        2245146419012221464653229454837455973318717872714603666108574522337672) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 160 = 0 +
    160 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 26 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (160 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_160 :
    recurrence5Scalar1First.coeff 160 =
      -((((((14 * 10 ^ 70 +
        0861247955897046877455419930664509292237301861128548037740368662940044) * 10 ^ 70 +
        0939628854994825288298995333606105027126130014954386019516596383124081) * 10 ^ 70 +
        1870186190812245153655368424517483137251647275788452082162804567749742) * 10 ^ 70 +
        1879076901019900675182066840223134120849830589144313975771911772272965) * 10 ^ 70 +
        2157240041892452977564877322308144001348062617392849183273226716731418) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 161 = 0 +
    161 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 26 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (161 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_161 :
    recurrence5Scalar1First.coeff 161 =
      ((((((32 * 10 ^ 70 +
        6827284871297612203907957185646794899146376012015406725072825939732574) * 10 ^ 70 +
        3006336149687421546852898686305380674883778029101359217299553261862148) * 10 ^ 70 +
        3896325427084349617971707180759782340167382617484950125905000399725324) * 10 ^ 70 +
        1438043127592611772006845477852785176882912383846709818606952839679603) * 10 ^ 70 +
        4219509622513365507514853535869373129620770378556565748204891768954655) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 162 = 0 +
    162 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 26 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (162 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_162 :
    recurrence5Scalar1First.coeff 162 =
      -((((((74 * 10 ^ 70 +
        4578858682342250814600017627085549910697014086998182000842996930979927) * 10 ^ 70 +
        3974210279612068503917952885231856106430077003227760237156667837734085) * 10 ^ 70 +
        1873233435655353543176972187041444535131419221928769872136552426146207) * 10 ^ 70 +
        5858734948553910424710288926655843888437881467154788290205353884960444) * 10 ^ 70 +
        6186696735956803620406229360694233280303095195048624325745634182875089) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 163 = 0 +
    163 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 26 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (163 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_163 :
    recurrence5Scalar1First.coeff 163 =
      ((((((166 * 10 ^ 70 +
        5689120295750373261010188321451625827487352281070481989762298057976552) * 10 ^ 70 +
        1354078684430046331114877365947801376282889618759433217572243755340525) * 10 ^ 70 +
        3916180307711316213200392868278590467746853089059120378438041023514732) * 10 ^ 70 +
        9413695810080050138982594983445692306207966028518486388569949552071741) * 10 ^ 70 +
        0317786917261475139357558050818761121551533421520600009026515605579631) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 26 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (164 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_164 :
    recurrence5Scalar1First.coeff 164 =
      -((((((365 * 10 ^ 70 +
        9251410512084707464159634831307932686859265129787246450381947908539004) * 10 ^ 70 +
        7978001434514080721223988068280416851587955731519632810455510609123040) * 10 ^ 70 +
        6443024978879020800288016212385253195356495862852080987176420677804078) * 10 ^ 70 +
        0936513397049311343803045561556691579885375959531611922116124422201388) * 10 ^ 70 +
        3285537150050755787989491674809277189920086699973707885500494640310832) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 165 = 0 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 26 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (165 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_165 :
    recurrence5Scalar1First.coeff 165 =
      ((((((789 * 10 ^ 70 +
        4575136560907869392820858019814048136235503589274450901984076308467950) * 10 ^ 70 +
        3617411486566632396303875342480386959395068463254094209521330261247209) * 10 ^ 70 +
        7656299534351489422216268727080074531722197886630041194212916967405685) * 10 ^ 70 +
        3072598566343715249172642008915228703492272672249044820347858332958988) * 10 ^ 70 +
        2439400206321785660902076252560197677764428213535809168044255888330497) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 166 = 0 +
    166 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 26 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (166 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_166 :
    recurrence5Scalar1First.coeff 166 =
      -((((((1672 * 10 ^ 70 +
        7291000314921580928528870691479127785332174310215181223712315502779159) * 10 ^ 70 +
        0509877680424287040212017573851423819860886003832429802861699193398502) * 10 ^ 70 +
        0906785796578329431091748037775026338949928600207706259212593825957269) * 10 ^ 70 +
        3562081139034302134631416408331655045433068478663536969819085594336556) * 10 ^ 70 +
        4091933050341154846211850442009845021547554749970809288482533345926977) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 167 = 0 +
    167 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 26 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (167 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_167 :
    recurrence5Scalar1First.coeff 167 =
      ((((((3480 * 10 ^ 70 +
        9988071801944780218699557652908030323984105665055333933748130970914813) * 10 ^ 70 +
        8628567190511288819015087161677402313579691760514437254078679430377200) * 10 ^ 70 +
        5838220932195149812832687079513794029677143487506230215319247016716440) * 10 ^ 70 +
        1342414232885174717695127993192340353774128096504685527971208100367288) * 10 ^ 70 +
        6118532769969056194275464761118169484942241519937788894511348926556456) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 168 = 0 +
    168 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 26 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (168 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_168 :
    recurrence5Scalar1First.coeff 168 =
      -((((((7115 * 10 ^ 70 +
        1419588099408554119007077596218452862376910211929796387707002743446809) * 10 ^ 70 +
        4430383005890541551142308936457690660506776975160944725805773602080234) * 10 ^ 70 +
        3325969589374310154392926619302803689547441714044362289351158728983337) * 10 ^ 70 +
        6154786291763043510319597648228268127868499065075957687858135329936300) * 10 ^ 70 +
        9117822861577423887770289143463289194295926177037090792386630732916361) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 169 = 0 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 26 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (169 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_169 :
    recurrence5Scalar1First.coeff 169 =
      ((((((14285 * 10 ^ 70 +
        1119681948198329608574338440620490127591340219496101563628273074983833) * 10 ^ 70 +
        3075584592287473309894159682742152379734571796973608266628968184909006) * 10 ^ 70 +
        7345755287492052003898858811229518165232446146855809182060710418318840) * 10 ^ 70 +
        0877411876947166321493075150951846486867746263450409371704980967622207) * 10 ^ 70 +
        8547260055421104088451076439550021395743630387635788782542625172107208) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 170 = 0 +
    170 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 26 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (170 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_170 :
    recurrence5Scalar1First.coeff 170 =
      -((((((28172 * 10 ^ 70 +
        2789110433875337721236398094779166753201200226785918606490384012154734) * 10 ^ 70 +
        9196324729497086918511378712771921280293199189203646343715802559300068) * 10 ^ 70 +
        0383926119811352539137356335843319807405114310776291290829523297189937) * 10 ^ 70 +
        4212212341963386295645151721540995068940792955260733100760718430455323) * 10 ^ 70 +
        4217765069807526275987163194407810504803134775464049523425251920349516) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 171 = 0 +
    171 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 26 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (171 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_171 :
    recurrence5Scalar1First.coeff 171 =
      ((((((54577 * 10 ^ 70 +
        7116745155057686557354988323358880560270322986845846404382959145802397) * 10 ^ 70 +
        5314751331554255286593874610927022334492853563579640158185382747135348) * 10 ^ 70 +
        1096947366805672380774979500519968936057012193205941458758306254989843) * 10 ^ 70 +
        7380335674704694050004208675232673690642232570404115368581350931866800) * 10 ^ 70 +
        4707454650883082816997459965823268787435607230576211612747704570454754) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 172 = 0 +
    172 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 26 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (172 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_172 :
    recurrence5Scalar1First.coeff 172 =
      -((((((103867 * 10 ^ 70 +
        4120444406562898943513805092639948446924475869618562646864746484283642) * 10 ^ 70 +
        2047547742971358141556015887285109093646693998729906747488323908041908) * 10 ^ 70 +
        1531609576237301013789912259669821490635013842687326777917639246885637) * 10 ^ 70 +
        7685780883208125272645036567324805822226723897063000124207273918038081) * 10 ^ 70 +
        5936342580981876337799580647464805397185082547569413419458997489611646) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 173 = 0 +
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
    rw [show 45 = 26 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (173 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_173 :
    recurrence5Scalar1First.coeff 173 =
      ((((((194190 * 10 ^ 70 +
        6956497336885437109804888986834872975608867979661648011465398526657249) * 10 ^ 70 +
        1474567923994745098653193570420306313847076706693175590877484753279076) * 10 ^ 70 +
        4697324495328301065027326790959958390951816063045400086087375929656242) * 10 ^ 70 +
        3288645981644600486375050609373145967369134520032774367818172576977064) * 10 ^ 70 +
        7807417045885653112587096268804392646128094589566145179015758584436158) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 174 = 0 +
    174 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 26 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (174 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_174 :
    recurrence5Scalar1First.coeff 174 =
      -((((((356677 * 10 ^ 70 +
        6720181310788818636164883580741500865602569401646915617236523373220371) * 10 ^ 70 +
        5150479657800583276851428235323812430990994219931693840344089612590148) * 10 ^ 70 +
        9849612104309682906948644540002601095473775406682178350898528979607143) * 10 ^ 70 +
        0824404965986112801502296246361326532228273948460471383177897594024591) * 10 ^ 70 +
        2753363427461576572186328117835663780958866194079180780189873537103470) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 175 = 0 +
    175 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 26 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (175 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_175 :
    recurrence5Scalar1First.coeff 175 =
      ((((((643626 * 10 ^ 70 +
        4405252563387595225879375568333502183629957064236549100788037970406482) * 10 ^ 70 +
        4807970598343463767495323443498557691383512468034674955009522038057603) * 10 ^ 70 +
        8193770626183176430143664665215546418588446435468641582631987713585996) * 10 ^ 70 +
        2243157672568067539249618740536212800902223396119234809575153123879997) * 10 ^ 70 +
        2800006587151820685218805700830132704255603858190506438032553685046460) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 176 = 0 +
    176 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 26 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (176 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_176 :
    recurrence5Scalar1First.coeff 176 =
      -((((((1141071 * 10 ^ 70 +
        9963879016043586952297679054487825057452021547135592844256805773873960) * 10 ^ 70 +
        5832412705092035735184218799709688326231142882611960423727524227548631) * 10 ^ 70 +
        7699985542605021673389082861635931440573965541171971314935609451115034) * 10 ^ 70 +
        9022502008654273461571885028221095593114566897777813787335063819543216) * 10 ^ 70 +
        7809909956955450272776390360452296649559410020781548554859664793460935) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 177 = 0 +
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
    rw [show 49 = 26 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (177 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_177 :
    recurrence5Scalar1First.coeff 177 =
      ((((((1987572 * 10 ^ 70 +
        0079069250075935838566743558660153485895605466244011510780727291085377) * 10 ^ 70 +
        1099785981834094751602274420087570593677556787611922625825919489666288) * 10 ^ 70 +
        1733709634448640216806558112314854738219067446784061810269151915508685) * 10 ^ 70 +
        5784066096170047786502402537260719392269903053388411897756368947068421) * 10 ^ 70 +
        6067330471255648841824098538635417038213532203665476844216451088878747) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 178 = 0 +
    178 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 26 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (178 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_178 :
    recurrence5Scalar1First.coeff 178 =
      -((((((3401507 * 10 ^ 70 +
        1891410460175264069962472774757350575020054096897533063063397533511055) * 10 ^ 70 +
        2814320875834070836729963039503426345916485500244130609780315745801744) * 10 ^ 70 +
        5152648645544270249190518354126405590358749901362772652829821062393348) * 10 ^ 70 +
        1571541965518107188901413117610456093632385951494349867766136715878571) * 10 ^ 70 +
        0072078585930097268643494008307884055282621582553610522667315994656438) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 179 = 0 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (179 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_179 :
    recurrence5Scalar1First.coeff 179 =
      ((((((5719593 * 10 ^ 70 +
        8403575633258796093609858493062349573905125995479759920322366730422632) * 10 ^ 70 +
        4326315112894192784069075654841337338551411597274859808266110189409567) * 10 ^ 70 +
        9836848924220602484929611929351616489865585230438691160431264092976931) * 10 ^ 70 +
        9527785323224026784370836633689575266871413128191067129265461220011958) * 10 ^ 70 +
        4689000237405439572631818086634619464779223004396939963545325902393886) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 180 = 0 +
    180 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 26 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (180 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_180 :
    recurrence5Scalar1First.coeff 180 =
      -((((((9449510 * 10 ^ 70 +
        0900172527489708026004815896041357311088760583710955073949206016364913) * 10 ^ 70 +
        5519239152541578843538284521718270454938594009327262645572019378302144) * 10 ^ 70 +
        4322860413917477986914342635929457706165269751700044192737410657318643) * 10 ^ 70 +
        6450621740364605399764236946619020148511059124324320852169666501849381) * 10 ^ 70 +
        6863224410151704775537796628033350696417813425392973731720621180579239) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 181 = 0 +
    181 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 26 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (181 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_181 :
    recurrence5Scalar1First.coeff 181 =
      ((((((15339354 * 10 ^ 70 +
        8629859065297105430047867654055718984473561494131507418683020641146346) * 10 ^ 70 +
        3885474799670841933740252908345828167691965451997345729564348975937189) * 10 ^ 70 +
        4886223243474051803405561237665300829237303074824526006959949712764272) * 10 ^ 70 +
        4823741848913583901225279006935853142852613260262463518866426601765542) * 10 ^ 70 +
        8347583796630659968060200704746900913042050292397802793316643529550781) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 182 = 0 +
    182 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 26 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (182 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_182 :
    recurrence5Scalar1First.coeff 182 =
      -((((((24465846 * 10 ^ 70 +
        0143661166661881462742739735470623645902945018991184151100915646243973) * 10 ^ 70 +
        0877466286204010268880912250651544869812946088508905075364570516891803) * 10 ^ 70 +
        6909152159564291756874560294663333289891791881967279809521969103741305) * 10 ^ 70 +
        2218186279521929619598687409954039280415518029070811593850519524811062) * 10 ^ 70 +
        3154151117121354147644364151668897910233449317871130186164112372090824) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 183 = 0 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 26 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (183 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_183 :
    recurrence5Scalar1First.coeff 183 =
      ((((((38341446 * 10 ^ 70 +
        6684298410637106504433657955684219505631897031048355318613076616479001) * 10 ^ 70 +
        7958548951768093275784194289044851249953213137975371910193161519680890) * 10 ^ 70 +
        9975612970108164720316813766387838097105982424346682522417378287548930) * 10 ^ 70 +
        6223675477703434376423840759417626005916026871725570348372775277695225) * 10 ^ 70 +
        9734476175008915156820825826397644620502588794302528037468866595831340) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 184 = 0 +
    184 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 26 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (184 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_184 :
    recurrence5Scalar1First.coeff 184 =
      -((((((59037726 * 10 ^ 70 +
        3929354769679135000495903266971851780319752308590869311434851404162077) * 10 ^ 70 +
        1032807139580163768793647006077127102011999674748756394927554261913783) * 10 ^ 70 +
        2810285267242336171043776837934432345837752658051214436730605102426063) * 10 ^ 70 +
        0202123608255487985933189278201123091750720691622902904588366662655479) * 10 ^ 70 +
        9132696573637205233243289354498495864730488240184955870480785332152605) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 185 = 0 +
    185 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 26 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (185 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_185 :
    recurrence5Scalar1First.coeff 185 =
      ((((((89318043 * 10 ^ 70 +
        6485639699531540085868660467770835226631880078228231164469298822545867) * 10 ^ 70 +
        7820024745341771758597440633631391378903883234714251157879642544694675) * 10 ^ 70 +
        1206906833692437942286900062916445812925281540292534564096071499850626) * 10 ^ 70 +
        3660961694696466333016619034664579204898111657117945074549593815185011) * 10 ^ 70 +
        0214619152893635902344184151175097873779662354478105134730263710886162) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 186 = 0 +
    186 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 26 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (186 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_186 :
    recurrence5Scalar1First.coeff 186 =
      -((((((132767090 * 10 ^ 70 +
        1736790310364512150864722450470506106561679799362506704831251355852444) * 10 ^ 70 +
        9177478177691808252240034730995321455288266616104781368196014154047098) * 10 ^ 70 +
        5170359853431304554880005245736673267424975847491329799560745900417583) * 10 ^ 70 +
        7406917030371623482641401220669113893731262308690708962086960423923667) * 10 ^ 70 +
        3399755277525837450711206717393190887043074398115032959222048533551765) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 187 = 0 +
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
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (187 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_187 :
    recurrence5Scalar1First.coeff 187 =
      ((((((193898274 * 10 ^ 70 +
        3488750761240401601336934392272897668034697482639256377397364323352730) * 10 ^ 70 +
        1080494513619063486195874546116985931881569429871111642148605720441172) * 10 ^ 70 +
        2460850699934371267711893048376730368726414873128172755028566799994499) * 10 ^ 70 +
        4960412908823321585263221965647300916586106839118755127289529296429311) * 10 ^ 70 +
        6892785634363702916106704256720438599469452118984264757053913613922782) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 188 = 0 +
    188 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 26 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (188 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_188 :
    recurrence5Scalar1First.coeff 188 =
      -((((((278213043 * 10 ^ 70 +
        3763893541498054538363193074134020831586601466652365791062750236181341) * 10 ^ 70 +
        9563633495613862795644943123984245322187773075825309339696879411982868) * 10 ^ 70 +
        4161203103924835652831366587678027008710782360278506617277627080942635) * 10 ^ 70 +
        2611348089323338976269954916425608223251014125346127925656008843238093) * 10 ^ 70 +
        4867617793508410036419771964867866850828538034915851217341137939338639) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 189 = 0 +
    189 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 26 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (189 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_189 :
    recurrence5Scalar1First.coeff 189 =
      ((((((392180211 * 10 ^ 70 +
        9012554066037258678361407920489217115613377045120160862491066391766666) * 10 ^ 70 +
        7940391593752655870576401644926199924099061506140289609225357943895057) * 10 ^ 70 +
        5055666928999757907436699254674361029199141988471964769981109217921271) * 10 ^ 70 +
        9349491528900430178813431573232077194707757977103542095610525409355606) * 10 ^ 70 +
        1645357373757450880697617554712345799255592068935491884471334284134125) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 190 = 0 +
    190 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 26 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (190 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_190 :
    recurrence5Scalar1First.coeff 190 =
      -((((((543099765 * 10 ^ 70 +
        4040147206785307909610482410880550403800342860727060242831941588802468) * 10 ^ 70 +
        3320257616546746972120026005410316354598831895458359322829953860018761) * 10 ^ 70 +
        9862946553613731865791944720347331829047413697575626445152095919996541) * 10 ^ 70 +
        3797714244817386937033052789748738175996109944437711702599664367277172) * 10 ^ 70 +
        1762703277554183004221968110231723238032390495649190117635552595917259) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 191 = 0 +
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
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 26 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (191 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_191 :
    recurrence5Scalar1First.coeff 191 =
      ((((((738816312 * 10 ^ 70 +
        1113593829260188473041699494848987669556371348024038821648446501449851) * 10 ^ 70 +
        1957525928949198051183941270335472065103528290229217408598568557146955) * 10 ^ 70 +
        1467970333792300720518159061543831147998110846403034103738661586632622) * 10 ^ 70 +
        3494437431597950429923811899351891934059103274826716466595396993432929) * 10 ^ 70 +
        7771530725685850024689794048628834469531447809532206369312360287340552) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 192 = 0 +
    192 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 26 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (192 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_192 :
    recurrence5Scalar1First.coeff 192 =
      -((((((987254234 * 10 ^ 70 +
        8169284415772988928698696872796492735831151498887044137935155161028020) * 10 ^ 70 +
        3744407452596307353247354876458451554042404980947417224974886174395205) * 10 ^ 70 +
        0688371657859488232646872397432507043340366220531221332600224106801123) * 10 ^ 70 +
        5024365962848050423340089318148996495701043995382732638807304580234429) * 10 ^ 70 +
        9471566215126976571550495375029384781993776917567569333566827015293652) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 193 = 0 +
    193 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 26 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (193 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_193 :
    recurrence5Scalar1First.coeff 193 =
      ((((((1295761083 * 10 ^ 70 +
        3851208858931904205543838793254927303271184508087703765746900566034495) * 10 ^ 70 +
        8897059030666177663877785615222102492055462289938926097543468525204324) * 10 ^ 70 +
        6677215854681933456430615114195438115563944502405364205235280932643587) * 10 ^ 70 +
        1132168497073770699579513921157716668897868592231845079576622669779566) * 10 ^ 70 +
        4256250412544910021662797975319170223591530629576444713347939597909854) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 194 = 0 +
    194 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 26 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (194 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_194 :
    recurrence5Scalar1First.coeff 194 =
      -((((((1670268350 * 10 ^ 70 +
        9457385006229256882400361342158932051907256385367529007732605777801621) * 10 ^ 70 +
        9324064525037639174549691092154604116881961814006141516430133366106720) * 10 ^ 70 +
        9128608686390570124319880642402557030311118243345069912476644238319457) * 10 ^ 70 +
        6068386907285914072521128460083446380546788036460530468217151254721722) * 10 ^ 70 +
        1375362735602915315098370973878125550227367805849796081063230953374488) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 195 = 0 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 26 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (195 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_195 :
    recurrence5Scalar1First.coeff 195 =
      ((((((2114308552 * 10 ^ 70 +
        6465418401520903317444677386378639278626675188049537616277181225250101) * 10 ^ 70 +
        1846974091374205591605686564447082654692709570986702609591124696765392) * 10 ^ 70 +
        7319784660726744195574188812372722642731875625462360262382413291163679) * 10 ^ 70 +
        5919000793849875159055371388348034467251786669643325362674996956526173) * 10 ^ 70 +
        6265695133834382262117793093979470719734433614202090268259796532560520) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 196 = 0 +
    196 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 26 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (196 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_196 :
    recurrence5Scalar1First.coeff 196 =
      -((((((2627961735 * 10 ^ 70 +
        3399372156077828654803298915859156766296786675947594397514351610773930) * 10 ^ 70 +
        8011095984407595599501988700746068309574879691224336323027699938926482) * 10 ^ 70 +
        4182774510480166431414517214932145842416501804567059406518667383744434) * 10 ^ 70 +
        0900576893066910343399228550227063929017277621567418186380458157247312) * 10 ^ 70 +
        8903005273972384417306892709799161356559661276130853420738835950636535) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 197 = 0 +
    197 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 26 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (197 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_197 :
    recurrence5Scalar1First.coeff 197 =
      ((((((3206838578 * 10 ^ 70 +
        0173364728232425111673462697886272003598135096562465431218037325159270) * 10 ^ 70 +
        1534574551747601512649713287452645846150434109497158180809771106982861) * 10 ^ 70 +
        0261119948236186346348518656831313182121532698177400900428329649653627) * 10 ^ 70 +
        1070990821501638260450395651659337794626831808837989660150418855732890) * 10 ^ 70 +
        5666824145284953697058242649986018677638119028935232007328488727103016) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 198 = 0 +
    198 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 26 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (198 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_198 :
    recurrence5Scalar1First.coeff 198 =
      -((((((3841234956 * 10 ^ 70 +
        2203480349625745018590134461235091250277750366512686405702796671996625) * 10 ^ 70 +
        2442355470916074035605248451626867620272073396886173099633092144158600) * 10 ^ 70 +
        0658533300890481552618192616151569499531886172257920046076209495708979) * 10 ^ 70 +
        9065959131594953137530320172281704874340489073696201604150172638370242) * 10 ^ 70 +
        6256951318572850551031925700103268412060527572169087846097590337223691) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 199 = 0 +
    199 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 26 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (199 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_199 :
    recurrence5Scalar1First.coeff 199 =
      ((((((4515607386 * 10 ^ 70 +
        8252349865594140020551552303661862185232848491216361781062920677813992) * 10 ^ 70 +
        1888676742328486121270219954105039284547515475965928576037058594645225) * 10 ^ 70 +
        0520924965251348273282963610747051843776383391046860271066420091545720) * 10 ^ 70 +
        6702390261930564379117199284509497954913956888771911956049671545324247) * 10 ^ 70 +
        9271169593082534475634438809707523038096483178368803129023340366474303) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 200 = 0 +
    200 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 26 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (200 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_200 :
    recurrence5Scalar1First.coeff 200 =
      -((((((5208513817 * 10 ^ 70 +
        1751559145729882177724467285039951123970756505922277474693237826919993) * 10 ^ 70 +
        0220977678922377611482235811818166048743820282362747994107557254518941) * 10 ^ 70 +
        0416340165811939882467092807260260873352891092549923219795084585360441) * 10 ^ 70 +
        4612167038508846245041890453499612108454655935957498154151769559532891) * 10 ^ 70 +
        9653487709109433931447765220211984984312706297583844618807063056607044) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 201 = 0 +
    201 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 26 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (201 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_201 :
    recurrence5Scalar1First.coeff 201 =
      ((((((5893135461 * 10 ^ 70 +
        1796262521442511608105289687386476181397049099388782534452251348668678) * 10 ^ 70 +
        0102403197995172437057542662755628522430687062791369258043305216577398) * 10 ^ 70 +
        8075757282638080994627844826402665547270402972163362912596933624651229) * 10 ^ 70 +
        7348093052527698944571046109843576333418780354331001770648850490479125) * 10 ^ 70 +
        7049043268061827010469477883733414209752942240779886184112459857330522) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 202 = 0 +
    202 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 26 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (202 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_202 :
    recurrence5Scalar1First.coeff 202 =
      -((((((6538441950 * 10 ^ 70 +
        0291300320198007005883918835234561488042068155985157545687228317826643) * 10 ^ 70 +
        3414254963620943160723156071534150313754879575493796965368921967803668) * 10 ^ 70 +
        2092634183267878644190057540255740934853515965080370799204900061860790) * 10 ^ 70 +
        9031381993846141793041597575067254143877442859911186521331225796313534) * 10 ^ 70 +
        9214805906340154270851518436420107387954599306815347531439443952377380) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 203 = 0 +
    203 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 26 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (203 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_203 :
    recurrence5Scalar1First.coeff 203 =
      ((((((7110987566 * 10 ^ 70 +
        1913624227049615073528724273193381455197229497354697024989524280867458) * 10 ^ 70 +
        7031804654797367663982917084334948055184538942319312257201027654814410) * 10 ^ 70 +
        5589102250907948098692814650878376031223729140285406890172955133942662) * 10 ^ 70 +
        2863923107946767903632153949320725319919806805901844405408362714976177) * 10 ^ 70 +
        0438338337010420395023120169693534279124118428833235947185315834299622) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 204 = 0 +
    204 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 26 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (204 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_204 :
    recurrence5Scalar1First.coeff 204 =
      -((((((7577239116 * 10 ^ 70 +
        5197291147157876451044808732803473865139284470634056935880581906312103) * 10 ^ 70 +
        7903697595587733849854791763180781490755489546344579202135338312054276) * 10 ^ 70 +
        9034646324068152156179376069807647519449298013378900894109930658533776) * 10 ^ 70 +
        0639003706077947210783609774451943958697189005881802539605337389949050) * 10 ^ 70 +
        4466072084965543012841388484051096061229972463372343685662634640638109) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 205 = 0 +
    205 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
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
    rw [show 77 = 26 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (205 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_205 :
    recurrence5Scalar1First.coeff 205 =
      ((((((7906248436 * 10 ^ 70 +
        3217119855203330097876793503296416794573664478627339519914774574814010) * 10 ^ 70 +
        7870236262339957659508747795158532584699200851737935858030576009447859) * 10 ^ 70 +
        5562006413642773362687917882980047725679083910171707486033333118802551) * 10 ^ 70 +
        4460065794517861128078674377161530244445434415061376051751939953491873) * 10 ^ 70 +
        0884089015494777655280191134838921156558950479350230035326082087962345) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 206 = 0 +
    206 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 26 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (206 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_206 :
    recurrence5Scalar1First.coeff 206 =
      -((((((8072409222 * 10 ^ 70 +
        1901086579729513573688328304781893434893658652530698444349273171974533) * 10 ^ 70 +
        8034412934349725305130795685206430740498048341162623472623355578056485) * 10 ^ 70 +
        2862652164795050371183489395306320577650978589961872614917593602350573) * 10 ^ 70 +
        7938312104381686048715904227581347114024495773532362693763115934951976) * 10 ^ 70 +
        1755221568180402057781972410276461932665946077977645373379363538793512) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 207 = 0 +
    207 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 26 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (207 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_207 :
    recurrence5Scalar1First.coeff 207 =
      ((((((8057993187 * 10 ^ 70 +
        8242523605345971190032706087716770663451211658118556090071300773064576) * 10 ^ 70 +
        9975916804795895813904258435460080234211803758688718407682372927295944) * 10 ^ 70 +
        2964627704808166327689738743662434132033996272594497828183886334263769) * 10 ^ 70 +
        6286491510153814743263498920427617429212405126591925610893251363553555) * 10 ^ 70 +
        2877642560211683667032798820626265242260706011448024198777627594655746) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 208 = 0 +
    208 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 26 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (208 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_208 :
    recurrence5Scalar1First.coeff 208 =
      -((((((7855155542 * 10 ^ 70 +
        9417214341889542476450589910659372086672566661817432728301650344442283) * 10 ^ 70 +
        0360063916423757968986381089092534571477246266866995096834639143656028) * 10 ^ 70 +
        2086680380299382952581578131960772657891859633024570000395869974579196) * 10 ^ 70 +
        5706292230834124105446109537700990635031578728761596352734443614219273) * 10 ^ 70 +
        4588384163145128536615767015905008967851846706858044818971892402958243) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 209 = 0 +
    209 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
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
    rw [show 81 = 26 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (209 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_209 :
    recurrence5Scalar1First.coeff 209 =
      ((((((7467139806 * 10 ^ 70 +
        5780174956118981641370887698419039802725262433215760611881234787807159) * 10 ^ 70 +
        1663021281895325637192897311990977078928736239283868669221385567337237) * 10 ^ 70 +
        5003917108272337020491199755393797440914462012126769330207970938431003) * 10 ^ 70 +
        7695234095270866223886349592820433174919640658060074728155279122900685) * 10 ^ 70 +
        3391485222482785750361750458008893276760330118164230751199750389398639) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 210 = 0 +
    210 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 26 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (210 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_210 :
    recurrence5Scalar1First.coeff 210 =
      -((((((6908494753 * 10 ^ 70 +
        3509291741487860635553214088098688658892389657499597102666286194580413) * 10 ^ 70 +
        7424177155166796973971228322679020672011179790418317389638819116000352) * 10 ^ 70 +
        7760907371624213978032895441020526643216220121444981471745048938967095) * 10 ^ 70 +
        9068871479417476031917661337061498057095018135737692482844129496542041) * 10 ^ 70 +
        3123477463204868996100530288818742068816728741047940018251974354145855) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 211 = 0 +
    211 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 26 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (211 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_211 :
    recurrence5Scalar1First.coeff 211 =
      ((((((6204231811 * 10 ^ 70 +
        4000827400872709616964494355538786288584421011567051928739794029979597) * 10 ^ 70 +
        4137454689236479778530806429163324738679536918084032574900061757971357) * 10 ^ 70 +
        1590455374134709825952925803980150332481906637589273495816126490882943) * 10 ^ 70 +
        4052263070888613416425548483468186945848115856571946513130975045676888) * 10 ^ 70 +
        7082070289033444372202088633652398507429088239165500930955133038328110) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 212 = 0 +
    212 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 26 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (212 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_212 :
    recurrence5Scalar1First.coeff 212 =
      -((((((5387982952 * 10 ^ 70 +
        8486959036498659787530795245324502496158792883386790178685083050579638) * 10 ^ 70 +
        2821268703646673904621024340313799405696360506621686765077862534979867) * 10 ^ 70 +
        5039332313410794501934894814892819861056275791704755334563652687307897) * 10 ^ 70 +
        4013886238864461925550754568588473098005291394966401820504634366392564) * 10 ^ 70 +
        5949015246896409242734889651697664523505247405803532772559623919114586) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 213 = 0 +
    213 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 26 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (213 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_213 :
    recurrence5Scalar1First.coeff 213 =
      ((((((4499346795 * 10 ^ 70 +
        1222226726058061380588864178632347144006563012588399185061188055190452) * 10 ^ 70 +
        8737211799019432741744303172923613385073775671319922155512887744315054) * 10 ^ 70 +
        2682378141099257888656350623855294981055276581669827605850430284773560) * 10 ^ 70 +
        4925999937394022949053468996607696058701348152080899333999834011687820) * 10 ^ 70 +
        9787329637272277389605840900228958869853945542194412191641072885923046) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 214 = 0 +
    214 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 26 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (214 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_214 :
    recurrence5Scalar1First.coeff 214 =
      -((((((3580713991 * 10 ^ 70 +
        1944763633669761528043395299286397455191362504853059581008087142613053) * 10 ^ 70 +
        2639238270442539916550283066274359680456555538237418873027267438462599) * 10 ^ 70 +
        2847568852832134403877431494042818731752485302980423704365193967458222) * 10 ^ 70 +
        3015369905555403210690423246369987663614454261753294535246393925420565) * 10 ^ 70 +
        9619506661034416038265349462400387001899250761652030522050170115061968) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 215 = 0 +
    215 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 26 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (215 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_215 :
    recurrence5Scalar1First.coeff 215 =
      ((((((2673925561 * 10 ^ 70 +
        4196216206697819582203051929014366977372042464376502868797048790996736) * 10 ^ 70 +
        3894676170742633998428964954626634912758348642206212091461260989079376) * 10 ^ 70 +
        1665530188907545866312695314480126281588943612710523902626196402471760) * 10 ^ 70 +
        8105756472662890290112101554048268072275337535187427833602530602236582) * 10 ^ 70 +
        0903163721131406717057437842857384149198982713680457226479342355292035) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 216 = 0 +
    216 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 26 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (216 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_216 :
    recurrence5Scalar1First.coeff 216 =
      -((((((1817130084 * 10 ^ 70 +
        4765070570878638598107520127187721560837110510780371529677552573778618) * 10 ^ 70 +
        2442657081105526210848443873092492438543175431017732871345640002647431) * 10 ^ 70 +
        0391862905406200102552765540340369551948824379140593401842289584552545) * 10 ^ 70 +
        5722024354759555928761084665789093214684522787959771038528626035200966) * 10 ^ 70 +
        3141999191655551516866089880791053844731684478561428003347941249507323) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 217 = 0 +
    217 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 26 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (217 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_217 :
    recurrence5Scalar1First.coeff 217 =
      ((((((1042166786 * 10 ^ 70 +
        9714083735609125131544764258812929077895572138211268023450892353316538) * 10 ^ 70 +
        8211509472567083148755340809488054459281312062261043630644070638685783) * 10 ^ 70 +
        0958085894376163943381046724677963204767523896368314144451887591717765) * 10 ^ 70 +
        4289128348650206389545389696164242303736106990664309131036442446136260) * 10 ^ 70 +
        9505810660407140281719854989062649377312905864225857617684431205495326) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 218 = 0 +
    218 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 26 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (218 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_218 :
    recurrence5Scalar1First.coeff 218 =
      -((((((372719393 * 10 ^ 70 +
        8649882912349107463480323940820090973461973212654863585472471013731768) * 10 ^ 70 +
        0113570519725671526635669177614581229772269817889399874840622195927197) * 10 ^ 70 +
        5029191081232869750175086653897571913755321148481776323831471987048878) * 10 ^ 70 +
        7462118253019616885280207817702073617781976324892455422425401374905699) * 10 ^ 70 +
        9423147806887945856294586878114850868565642912872785438751153051863912) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 219 = 0 +
    219 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
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
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (219 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_219 :
    recurrence5Scalar1First.coeff 219 =
      -((((((176625097 * 10 ^ 70 +
        9055082972459972200630153281327092263725593222715907645462060111025473) * 10 ^ 70 +
        4807419048530039291170013787999435041802469969485180280853453412179871) * 10 ^ 70 +
        4353118367208060353939242291028280711143413591561627179121853917851616) * 10 ^ 70 +
        9634800287325989972416898116712409733320943186967277152590159314564836) * 10 ^ 70 +
        0180413710071007098052315724365965731035879891840126808187713092022207) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 220 = 0 +
    220 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 26 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (220 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_220 :
    recurrence5Scalar1First.coeff 220 =
      ((((((600399113 * 10 ^ 70 +
        2295345586407675815478678279651300327255992209819305969268665924992468) * 10 ^ 70 +
        0274864063747804394937772294934242807923378240104999100251293985627565) * 10 ^ 70 +
        6857543407890485184063102422753119931917612449710281327295646664272981) * 10 ^ 70 +
        8006581985964861235746590249061721999522434429996281209049839240955731) * 10 ^ 70 +
        3619503606161209397861077440902912861100696262649601846517375538389374) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 221 = 0 +
    221 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 26 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence5Scalar1First_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder6Coefficient0.coeff (154 + x) *
        recurrence5B2A3.coeff (221 - (154 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5B0_coeff_high (154 + x) (by omega)]
  norm_num

theorem recurrence5Scalar1First_coeff_221 :
    recurrence5Scalar1First.coeff 221 =
      -((((((901456527 * 10 ^ 70 +
        6143077338653172402302141111940489493320412335702340763021874806654128) * 10 ^ 70 +
        4791580214442559705185053828645213382350372827247688731880136153738236) * 10 ^ 70 +
        4051056298239769723420718570583090155576843499360863134555768235771318) * 10 ^ 70 +
        6371788766000356327842768907050932178482277793214088293415290110106801) * 10 ^ 70 +
        7737916257909830441965002876259760593924204456477441294449232848243020) : ℚ) := by
  unfold recurrence5Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 222 = 0 +
    222 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 26 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar1First_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
