/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Left coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2LeadingSquare_coeff_0
  recurrence2LeadingSquare_coeff_1
  recurrence2LeadingSquare_coeff_2
  recurrence2LeadingSquare_coeff_3
  recurrence2LeadingSquare_coeff_4
  recurrence2LeadingSquare_coeff_5
  recurrence2LeadingSquare_coeff_6
  recurrence2LeadingSquare_coeff_7
  recurrence2LeadingSquare_coeff_8
  recurrence2LeadingSquare_coeff_9
  recurrence2LeadingSquare_coeff_10
  recurrence2LeadingSquare_coeff_11
  recurrence2LeadingSquare_coeff_12
  recurrence2LeadingSquare_coeff_13
  recurrence2LeadingSquare_coeff_14
  recurrence2LeadingSquare_coeff_15
  recurrence2LeadingSquare_coeff_16
  recurrence2LeadingSquare_coeff_17
  recurrence2LeadingSquare_coeff_18
  recurrence2LeadingSquare_coeff_19
  recurrence2LeadingSquare_coeff_20
  recurrence2LeadingSquare_coeff_21
  recurrence2LeadingSquare_coeff_22
  recurrence2LeadingSquare_coeff_23
  recurrence2LeadingSquare_coeff_24
  recurrence2LeadingSquare_coeff_25
  recurrence2LeadingSquare_coeff_26
  recurrence2LeadingSquare_coeff_27
  recurrence2LeadingSquare_coeff_28
  recurrence2LeadingSquare_coeff_29
  recurrence2LeadingSquare_coeff_30
  recurrence2LeadingSquare_coeff_31
  recurrence2LeadingSquare_coeff_32
  recurrence2LeadingSquare_coeff_33
  recurrence2LeadingSquare_coeff_34
  recurrence2LeadingSquare_coeff_35
  recurrence2LeadingSquare_coeff_36
  recurrence2LeadingSquare_coeff_37
  recurrence2LeadingSquare_coeff_38
  recurrence2LeadingSquare_coeff_39
  recurrence2LeadingSquare_coeff_40
  recurrence2LeadingSquare_coeff_41
  recurrence2LeadingSquare_coeff_42
  recurrence2LeadingSquare_coeff_43
  recurrence2LeadingSquare_coeff_44
  recurrence2LeadingSquare_coeff_45
  recurrence2LeadingSquare_coeff_46
  recurrence2LeadingSquare_coeff_47
  recurrence2LeadingSquare_coeff_48
  recurrence2LeadingSquare_coeff_49
  recurrence2LeadingSquare_coeff_50
  recurrence2LeadingSquare_coeff_51
  recurrence2LeadingSquare_coeff_52
  recurrence2LeadingSquare_coeff_53
  recurrence2LeadingSquare_coeff_54
  recurrence2LeadingSquare_coeff_55
  recurrence2LeadingSquare_coeff_56
  recurrence2LeadingSquare_coeff_57
  recurrence2LeadingSquare_coeff_58
  recurrence2LeadingSquare_coeff_59
  recurrence2LeadingSquare_coeff_60
  recurrence2LeadingSquare_coeff_61
  recurrence2LeadingSquare_coeff_62
  recurrence2LeadingSquare_coeff_63
  recurrence2LeadingSquare_coeff_64
  recurrence2LeadingSquare_coeff_65
  recurrence2LeadingSquare_coeff_66
  recurrence2LeadingSquare_coeff_67
  recurrence2LeadingSquare_coeff_68
  recurrence2LeadingSquare_coeff_69
  recurrence2LeadingSquare_coeff_70
  recurrence2LeadingSquare_coeff_71
  recurrence2LeadingSquare_coeff_72
  recurrence2LeadingSquare_coeff_73
  recurrence2LeadingSquare_coeff_74
  recurrence2LeadingSquare_coeff_75
  recurrence2LeadingSquare_coeff_76
  recurrence2LeadingSquare_coeff_77
  recurrence2LeadingSquare_coeff_78
  recurrence2LeadingSquare_coeff_79
  recurrence2LeadingSquare_coeff_80
  recurrence2LeadingSquare_coeff_81
  recurrence2LeadingSquare_coeff_82
  recurrence2LeadingSquare_coeff_83
  recurrence2LeadingSquare_coeff_84
  recurrence2LeadingSquare_coeff_85
  recurrence2LeadingSquare_coeff_86
  recurrence2LeadingSquare_coeff_87
  recurrence2LeadingSquare_coeff_88
  recurrence2LeadingSquare_coeff_89
  recurrence2LeadingSquare_coeff_90
  recurrence2LeadingSquare_coeff_91
  recurrence2LeadingSquare_coeff_92
  recurrence2LeadingSquare_coeff_93
  recurrence2LeadingSquare_coeff_94
  recurrence2LeadingSquare_coeff_95
  recurrence2LeadingSquare_coeff_96
  recurrence2LeadingSquare_coeff_97
  recurrence2LeadingSquare_coeff_98
  recurrence2LeadingSquare_coeff_99
  recurrence2LeadingSquare_coeff_100
  recurrence2LeadingSquare_coeff_101
  recurrence2LeadingSquare_coeff_102
  recurrence2LeadingSquare_coeff_103
  recurrence2LeadingSquare_coeff_104
  recurrence2LeadingSquare_coeff_105
  recurrence2LeadingSquare_coeff_106
  recurrence2LeadingSquare_coeff_107
  recurrence2LeadingSquare_coeff_108
  recurrence2LeadingSquare_coeff_109
  recurrence2LeadingSquare_coeff_110
  recurrence2LeadingSquare_coeff_111
  recurrence2LeadingSquare_coeff_112
  recurrence2LeadingSquare_coeff_113
  recurrence2LeadingSquare_coeff_114
  recurrence2LeadingSquare_coeff_115
  recurrence2LeadingSquare_coeff_116
  recurrence2LeadingSquare_coeff_117
  recurrence2LeadingSquare_coeff_118
  recurrence2LeadingSquare_coeff_119
  recurrence2LeadingSquare_coeff_120
  recurrence2LeadingSquare_coeff_121
  recurrence2LeadingSquare_coeff_122
  recurrence2LeadingSquare_coeff_123
  recurrence2LeadingSquare_coeff_124
  recurrence2LeadingSquare_coeff_125
  recurrence2LeadingSquare_coeff_126
  recurrence2LeadingSquare_coeff_127
  recurrence2LeadingSquare_coeff_128
  recurrence2LeadingSquare_coeff_129
  recurrence2LeadingSquare_coeff_130
  recurrence2LeadingSquare_coeff_131
  recurrence2LeadingSquare_coeff_132
  recurrence2LeadingSquare_coeff_133
  recurrence2LeadingSquare_coeff_134
  recurrence2LeadingSquare_coeff_135
  recurrence2LeadingSquare_coeff_136
  recurrence2LeadingSquare_coeff_137
  recurrence2LeadingSquare_coeff_138
  recurrence2LeadingSquare_coeff_139
  recurrence2LeadingSquare_coeff_140
  recurrence2LeadingSquare_coeff_141
  recurrence2LeadingSquare_coeff_142
  recurrence2LeadingSquare_coeff_143
  recurrence2LeadingSquare_coeff_144
  recurrence2LeadingSquare_coeff_145
  recurrence2LeadingSquare_coeff_146
  recurrence2LeadingSquare_coeff_147
  recurrence2LeadingSquare_coeff_148
  recurrence2LeadingSquare_coeff_149
  recurrence2LeadingSquare_coeff_150
  recurrence2LeadingSquare_coeff_151
  recurrence2LeadingSquare_coeff_152
  recurrence2LeadingSquare_coeff_153
  recurrence2LeadingSquare_coeff_154
  recurrence2LeadingSquare_coeff_155
  recurrence2LeadingSquare_coeff_156
  recurrence2LeadingSquare_coeff_157
  recurrence2LeadingSquare_coeff_158
  recurrence2LeadingSquare_coeff_159
  recurrence2LeadingSquare_coeff_160
  recurrence2LeadingSquare_coeff_161
  recurrence2LeadingSquare_coeff_162
  recurrence2LeadingSquare_coeff_163
  recurrence2LeadingSquare_coeff_164
  recurrence2LeadingSquare_coeff_165
  recurrence2LeadingSquare_coeff_166
  recurrence2LeadingSquare_coeff_167
  recurrence2LeadingSquare_coeff_168
  recurrence2LeadingSquare_coeff_169
  recurrence2LeadingSquare_coeff_170
  recurrence2LeadingSquare_coeff_171
  recurrence2LeadingSquare_coeff_172
  recurrence2LeadingSquare_coeff_173
  recurrence2LeadingSquare_coeff_174
  recurrence2LeadingSquare_coeff_175
  recurrence2LeadingSquare_coeff_176
  recurrence2LeadingSquare_coeff_177
  recurrence2LeadingSquare_coeff_178
  recurrence2LeadingSquare_coeff_179
  recurrence2LeadingSquare_coeff_180
  recurrence2LeadingSquare_coeff_181
  recurrence2LeadingSquare_coeff_182
  recurrence2LeadingSquare_coeff_183
  recurrence2LeadingSquare_coeff_184
  recurrence2LeadingSquare_coeff_185
  recurrence2LeadingSquare_coeff_186
  recurrence2LeadingSquare_coeff_187
  recurrence2LeadingSquare_coeff_188
  recurrence2LeadingSquare_coeff_189
  recurrence2LeadingSquare_coeff_190
  recurrence2LeadingSquare_coeff_191
  recurrence2LeadingSquare_coeff_192
  recurrence2LeadingSquare_coeff_193
  recurrence2LeadingSquare_coeff_194
  recurrence2LeadingSquare_coeff_195
  recurrence2LeadingSquare_coeff_196
  recurrence2LeadingSquare_coeff_197
  recurrence2LeadingSquare_coeff_198
  recurrence2LeadingSquare_coeff_199
  recurrence2LeadingSquare_coeff_200
  recurrence2LeadingSquare_coeff_201
  recurrence2LeadingSquare_coeff_202
  recurrence2LeadingSquare_coeff_203
  recurrence2LeadingSquare_coeff_204
  recurrence2LeadingSquare_coeff_205
  recurrence2LeadingSquare_coeff_206
  recurrence2LeadingSquare_coeff_207
  recurrence2LeadingSquare_coeff_208
  recurrence2LeadingSquare_coeff_209
  recurrence2LeadingSquare_coeff_210
  recurrence2LeadingSquare_coeff_211
  recurrence2LeadingSquare_coeff_212
  recurrence2LeadingSquare_coeff_213
  recurrence2LeadingSquare_coeff_214
  recurrence2LeadingSquare_coeff_215
  recurrence2LeadingSquare_coeff_216
  recurrence2LeadingSquare_coeff_217
  recurrence2LeadingSquare_coeff_218
  recurrence2LeadingSquare_coeff_219
  recurrence2LeadingSquare_coeff_220
  recurrence2LeadingSquare_coeff_221
  recurrence2LeadingSquare_coeff_222
  recurrence2LeadingSquare_coeff_223
  recurrence2LeadingSquare_coeff_224
  recurrence2LeadingSquare_coeff_225
  recurrence2LeadingSquare_coeff_226
  recurrence2LeadingSquare_coeff_227
  recurrence2LeadingSquare_coeff_228
  recurrence2LeadingSquare_coeff_229
  recurrence2LeadingSquare_coeff_230
  recurrence2LeadingSquare_coeff_231
  recurrence2LeadingSquare_coeff_232
  recurrence2LeadingSquare_coeff_233
  recurrence2LeadingSquare_coeff_234
  recurrence2LeadingSquare_coeff_235
  recurrence2LeadingSquare_coeff_236
  recurrence2LeadingSquare_coeff_237
  recurrence2LeadingSquare_coeff_238
  recurrence2LeadingSquare_coeff_239
  recurrence2LeadingSquare_coeff_240
  recurrence2LeadingSquare_coeff_241
  recurrence2LeadingSquare_coeff_242
  recurrence2LeadingSquare_coeff_243
  recurrence2LeadingSquare_coeff_244
  recurrence2LeadingSquare_coeff_245
  recurrence2LeadingSquare_coeff_246
  recurrence2LeadingSquare_coeff_247
  recurrence2LeadingSquare_coeff_248
  recurrence2LeadingSquare_coeff_249
  recurrence2LeadingSquare_coeff_250
  recurrence2LeadingSquare_coeff_251
  recurrence2LeadingSquare_coeff_252
  recurrence2LeadingSquare_coeff_253
  recurrence2LeadingSquare_coeff_254
  recurrence2LeadingSquare_coeff_255
  recurrence2LeadingSquare_coeff_256
  recurrence2LeadingSquare_coeff_257
  recurrence2LeadingSquare_coeff_258
  recurrence2LeadingSquare_coeff_259
  recurrence2LeadingSquare_coeff_260
  recurrence2LeadingSquare_coeff_261
  recurrence2LeadingSquare_coeff_262
  recurrence2LeadingSquare_coeff_263
  recurrence2LeadingSquare_coeff_264
  recurrence2LeadingSquare_coeff_265
  recurrence2LeadingSquare_coeff_266
  recurrence2LeadingSquare_coeff_267
  recurrence2LeadingSquare_coeff_268
  recurrence2A2_coeff_0
  recurrence2A2_coeff_1
  recurrence2A2_coeff_2
  recurrence2A2_coeff_3
  recurrence2A2_coeff_4
  recurrence2A2_coeff_5
  recurrence2A2_coeff_6
  recurrence2A2_coeff_7
  recurrence2A2_coeff_8
  recurrence2A2_coeff_9
  recurrence2A2_coeff_10
  recurrence2A2_coeff_11
  recurrence2A2_coeff_12
  recurrence2A2_coeff_13
  recurrence2A2_coeff_14
  recurrence2A2_coeff_15
  recurrence2A2_coeff_16
  recurrence2A2_coeff_17
  recurrence2A2_coeff_18
  recurrence2A2_coeff_19
  recurrence2A2_coeff_20
  recurrence2A2_coeff_21
  recurrence2A2_coeff_22
  recurrence2A2_coeff_23
  recurrence2A2_coeff_24
  recurrence2A2_coeff_25
  recurrence2A2_coeff_26
  recurrence2A2_coeff_27
  recurrence2A2_coeff_28
  recurrence2A2_coeff_29
  recurrence2A2_coeff_30
  recurrence2A2_coeff_31
  recurrence2A2_coeff_32
  recurrence2A2_coeff_33
  recurrence2A2_coeff_34
  recurrence2A2_coeff_35
  recurrence2A2_coeff_36
  recurrence2A2_coeff_37
  recurrence2A2_coeff_38
  recurrence2A2_coeff_39
  recurrence2A2_coeff_40
  recurrence2A2_coeff_41
  recurrence2A2_coeff_42
  recurrence2A2_coeff_43
  recurrence2A2_coeff_44
  recurrence2A2_coeff_45
  recurrence2A2_coeff_46
  recurrence2A2_coeff_47
  recurrence2A2_coeff_48
  recurrence2A2_coeff_49
  recurrence2A2_coeff_50
  recurrence2A2_coeff_51
  recurrence2A2_coeff_52
  recurrence2A2_coeff_53
  recurrence2A2_coeff_54
  recurrence2A2_coeff_55
  recurrence2A2_coeff_56
  recurrence2A2_coeff_57
  recurrence2A2_coeff_58
  recurrence2A2_coeff_59
  recurrence2A2_coeff_60
  recurrence2A2_coeff_61
  recurrence2A2_coeff_62
  recurrence2A2_coeff_63
  recurrence2A2_coeff_64
  recurrence2A2_coeff_65
  recurrence2A2_coeff_66
  recurrence2A2_coeff_67
  recurrence2A2_coeff_68
  recurrence2A2_coeff_69
  recurrence2A2_coeff_70
  recurrence2A2_coeff_71
  recurrence2A2_coeff_72
  recurrence2A2_coeff_73
  recurrence2A2_coeff_74
  recurrence2A2_coeff_75
  recurrence2A2_coeff_76
  recurrence2A2_coeff_77
  recurrence2A2_coeff_78
  recurrence2A2_coeff_79
  recurrence2A2_coeff_80
  recurrence2A2_coeff_81
  recurrence2A2_coeff_82
  recurrence2A2_coeff_83
  recurrence2A2_coeff_84
  recurrence2A2_coeff_85
  recurrence2A2_coeff_86
  recurrence2A2_coeff_87
  recurrence2A2_coeff_88
  recurrence2A2_coeff_89
  recurrence2A2_coeff_90
  recurrence2A2_coeff_91
  recurrence2A2_coeff_92
  recurrence2A2_coeff_93
  recurrence2A2_coeff_94
  recurrence2A2_coeff_95
  recurrence2A2_coeff_96
  recurrence2A2_coeff_97
  recurrence2A2_coeff_98
  recurrence2A2_coeff_99
  recurrence2A2_coeff_100
  recurrence2A2_coeff_101
  recurrence2A2_coeff_102
  recurrence2A2_coeff_103
  recurrence2A2_coeff_104
  recurrence2A2_coeff_105
  recurrence2A2_coeff_106
  recurrence2A2_coeff_107
  recurrence2A2_coeff_108
  recurrence2A2_coeff_109
  recurrence2A2_coeff_110

theorem recurrence2Scalar2Left_coeff_0 :
    recurrence2Scalar2Left.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_1 :
    recurrence2Scalar2Left.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_2 :
    recurrence2Scalar2Left.coeff 2 =
      (-17666048 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_3 :
    recurrence2Scalar2Left.coeff 3 =
      (82521357824 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_4 :
    recurrence2Scalar2Left.coeff 4 =
      (-782071547254928 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_5 :
    recurrence2Scalar2Left.coeff 5 =
      (3638873756429128352 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_6 :
    recurrence2Scalar2Left.coeff 6 =
      (-10332149423322026186900 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_7 :
    recurrence2Scalar2Left.coeff 7 =
      (41776721686130278307439788 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_8 :
    recurrence2Scalar2Left.coeff 8 =
      (-36849241760995676829070403296 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_9 :
    recurrence2Scalar2Left.coeff 9 =
      (39244783291543746307241711906068 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_10 :
    recurrence2Scalar2Left.coeff 10 =
      (-22770580396744384690338764497727624 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_11 :
    recurrence2Scalar2Left.coeff 11 =
      (11873780753948200354594321214175649288 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_12 :
    recurrence2Scalar2Left.coeff 12 =
      (-4429712472032609267303881600519887610560 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_13 :
    recurrence2Scalar2Left.coeff 13 =
      (1148287396002910478251386187992009629191264 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_14 :
    recurrence2Scalar2Left.coeff 14 =
      (-191021702939796971530170117625053240675041292 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_15 :
    recurrence2Scalar2Left.coeff 15 =
      (9998144716367786294277747319860734507358318440 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_16 :
    recurrence2Scalar2Left.coeff 16 =
      (4732501139394818012306367452035613783097654228255 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_17 :
    recurrence2Scalar2Left.coeff 17 =
      (-1812091119128561210301831736676496175498699993815135 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_18 :
    recurrence2Scalar2Left.coeff 18 =
      (378690685673886036619807207687049595166157572171415991 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_19 :
    recurrence2Scalar2Left.coeff 19 =
      (-57174842791386928710168172767007480352299224331364920894 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_20 :
    recurrence2Scalar2Left.coeff 20 =
      (6723577334129949671353663609419532195265698844130069708723 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_21 :
    recurrence2Scalar2Left.coeff 21 =
      (-636410957586700950266416153543241328842386279902166349110079 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_22 :
    recurrence2Scalar2Left.coeff 22 =
      (49279122166220075856942806916083934076588802460118901047062131 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_23 :
    recurrence2Scalar2Left.coeff 23 =
      (-3141356932424340256959628646126677235682614562949567448726135529 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_24 :
    recurrence2Scalar2Left.coeff 24 =
      (164043259268026196826464210044682718050356127271614741008319444566 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_25 :
    recurrence2Scalar2Left.coeff 25 =
      (-6810820581522464204611018823123261868492805750661863680544038907698 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_26 :
    recurrence2Scalar2Left.coeff 26 =
      (199204769303213078352812901611840803658207612764553846549092396927566 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_27 :
    recurrence2Scalar2Left.coeff 27 =
      (-1302022068668396843872714665019058568957144029490432402437155033637645 : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_28 :
    recurrence2Scalar2Left.coeff 28 =
      -((33 * 10 ^ 70 +
        3838133925179813672492153826353337075304567535452539120881952670308309) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_29 :
    recurrence2Scalar2Left.coeff 29 =
      ((3031 * 10 ^ 70 +
        8982316213933172931260799295453661458331804370288076151457615769905996) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_30 :
    recurrence2Scalar2Left.coeff 30 =
      -((175304 * 10 ^ 70 +
        6560459217376421415707358271947129081119918449119402080764212038188293) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_31 :
    recurrence2Scalar2Left.coeff 31 =
      ((7787628 * 10 ^ 70 +
        3006805827568218854325395734304234866416680870367691163761828110089038) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar2Left_coeff_32 :
    recurrence2Scalar2Left.coeff 32 =
      -((269327317 * 10 ^ 70 +
        4075306712112791451845221884651347183009173936290998914957387240855447) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_33 :
    recurrence2Scalar2Left.coeff 33 =
      ((6541809176 * 10 ^ 70 +
        3648056723726815997188923470048973734329991210604183491372388423006807) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_34 :
    recurrence2Scalar2Left.coeff 34 =
      -((42757138888 * 10 ^ 70 +
        8903027972387753302307195372000729741661014214624176639855002191002703) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_35 :
    recurrence2Scalar2Left.coeff 35 =
      -((6514450474045 * 10 ^ 70 +
        3192117893236711817920234772389016650418524838897600282199218740338155) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_36 :
    recurrence2Scalar2Left.coeff 36 =
      ((487282175073455 * 10 ^ 70 +
        0929169693017287691475336309166371483048994511411900458505850020935487) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_37 :
    recurrence2Scalar2Left.coeff 37 =
      -((22746990136592715 * 10 ^ 70 +
        2730781420168240476997367043142698659815719543075170127956645024775154) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_38 :
    recurrence2Scalar2Left.coeff 38 =
      ((812271057511571795 * 10 ^ 70 +
        4458400888741861927271013787436781045597593404714804680231928848511432) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_39 :
    recurrence2Scalar2Left.coeff 39 =
      -((22541731383609462687 * 10 ^ 70 +
        8990525514577332299322862685042038255384553864361580077389218789685753) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_40 :
    recurrence2Scalar2Left.coeff 40 =
      ((448778547124029972947 * 10 ^ 70 +
        4551624909081664266421528977604579433001481737622606547350770774186464) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_41 :
    recurrence2Scalar2Left.coeff 41 =
      -((4044672538816681952742 * 10 ^ 70 +
        7388391609617100530953754659597661180929416956784555793271455221496193) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_42 :
    recurrence2Scalar2Left.coeff 42 =
      -((122952503385007611848133 * 10 ^ 70 +
        8010834268453708298271805782231255053693522128032343825650840474670167) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_43 :
    recurrence2Scalar2Left.coeff 43 =
      ((7391923306620800312375099 * 10 ^ 70 +
        2198312993390289347941944126866636909299643583810476732817135555444818) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_44 :
    recurrence2Scalar2Left.coeff 44 =
      -((219995366876803091568304114 * 10 ^ 70 +
        3463361958085961389493379767219358708263628868023025474972744194104623) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_45 :
    recurrence2Scalar2Left.coeff 45 =
      ((4710714825510915786422753400 * 10 ^ 70 +
        3426029699663490197900085542366679180804359748951766799914365160102551) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_46 :
    recurrence2Scalar2Left.coeff 46 =
      -((83276584457121403660242988188 * 10 ^ 70 +
        2753642487445998961139258492796128803323756979706528788221488999133186) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_47 :
    recurrence2Scalar2Left.coeff 47 =
      ((1542105123031731461618138312942 * 10 ^ 70 +
        3756465917016360841340251783368437535800707384058835177441468061990153) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_48 :
    recurrence2Scalar2Left.coeff 48 =
      -((39142665086015022902882868866820 * 10 ^ 70 +
        3013443689191911450299303976739900306050433706745716713590278213291840) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_49 :
    recurrence2Scalar2Left.coeff 49 =
      ((1195257042247813646643464523710336 * 10 ^ 70 +
        4330856921076860369075467300671817779076451844968421745059800859547543) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_50 :
    recurrence2Scalar2Left.coeff 50 =
      -((33980330113825803410981958771426073 * 10 ^ 70 +
        5327546812469453009198170603841581347349384836395315067314397849338345) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_51 :
    recurrence2Scalar2Left.coeff 51 =
      ((821105170909730501121708028373599740 * 10 ^ 70 +
        2721066529837215585347858212460993795280627888491296220333579306587340) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_52 :
    recurrence2Scalar2Left.coeff 52 =
      -((16648918692762438262616681173809013046 * 10 ^ 70 +
        7152029189423621187303587254148435373239505759865718799018285119488628) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_53 :
    recurrence2Scalar2Left.coeff 53 =
      ((282249230664182337650827168764921262309 * 10 ^ 70 +
        5951152207618325090756730401537707999687135413390656466914347344808031) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_54 :
    recurrence2Scalar2Left.coeff 54 =
      -((3898596611445870451703727890221121205401 * 10 ^ 70 +
        8176839286287074378699818914458924175043450621663852800965671552383847) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_55 :
    recurrence2Scalar2Left.coeff 55 =
      ((39204929340230800059014746262207335617234 * 10 ^ 70 +
        4586855524113787573172583804057544796535808793597798346109259468375797) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_56 :
    recurrence2Scalar2Left.coeff 56 =
      -((111766540798516298197587797323985213866934 * 10 ^ 70 +
        7731683656913586065327364178532773626901744464613147885696717914174952) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_57 :
    recurrence2Scalar2Left.coeff 57 =
      -((7203966099826935877280736865448943698449904 * 10 ^ 70 +
        1247361854292825335123535082797295258979360840062083481585038929543933) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_58 :
    recurrence2Scalar2Left.coeff 58 =
      ((244794217244704337141682671508798983517174205 * 10 ^ 70 +
        2624542390080919706790253655590521101320996641168797862689336957367861) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_59 :
    recurrence2Scalar2Left.coeff 59 =
      -((5398974594395137268743829891170197063539421426 * 10 ^ 70 +
        8302326666513492514817747338248817625866481735185303166318080047488212) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_60 :
    recurrence2Scalar2Left.coeff 60 =
      ((96817752849741796622419306456103367068640410324 * 10 ^ 70 +
        9547207725809411422483504997171492786090380746516259313933833927476901) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_61 :
    recurrence2Scalar2Left.coeff 61 =
      -((1486374858148276198311819067015716813059363513578 * 10 ^ 70 +
        6115442498009952592431153656773921228312460420801750750492024627954788) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_62 :
    recurrence2Scalar2Left.coeff 62 =
      ((19623413909393901991282353564704953304675805051053 * 10 ^ 70 +
        9755553930185972997973907000345848957314164033684708156423374296643950) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_63 :
    recurrence2Scalar2Left.coeff 63 =
      -((215586538084572651598016830715467217632451566690911 * 10 ^ 70 +
        3595689577481660966668588426351217937413935964778251900508817304858084) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_64 :
    recurrence2Scalar2Left.coeff 64 =
      ((1735170733468349916310043373257386695775276753848534 * 10 ^ 70 +
        9397532051696765058285243707519155696423362677533156186900583846025970) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_65 :
    recurrence2Scalar2Left.coeff 65 =
      -((3385907550573403540077628921048123691583102295166379 * 10 ^ 70 +
        3269464254339738817558900156816346321167023848335455818125330934842625) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_66 :
    recurrence2Scalar2Left.coeff 66 =
      -((232830205355849095414969789836458958940252547661402334 * 10 ^ 70 +
        0227559665032124906358251857521060197468535595261485256997776401892702) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_67 :
    recurrence2Scalar2Left.coeff 67 =
      ((6387567811206810542834182445575605036092758425854630370 * 10 ^ 70 +
        4909481620461424129553737735026533478579281692865057523290824979811046) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_68 :
    recurrence2Scalar2Left.coeff 68 =
      -((117102457676071340869968629944502007325374816305114451708 * 10 ^ 70 +
        5781987068130552883935802284006326635247692029542442623041496077927937) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_69 :
    recurrence2Scalar2Left.coeff 69 =
      ((1789262554301831334992147854737252764393645757492492191531 * 10 ^ 70 +
        5748676433739351192331594763648804784814593490200562024504534109012148) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_70 :
    recurrence2Scalar2Left.coeff 70 =
      -((24300803355724518334105100001941477544575780170732637549379 * 10 ^ 70 +
        4096610195963911085425294357272615553125428914201844896188045896533269) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_71 :
    recurrence2Scalar2Left.coeff 71 =
      ((301781199392324330030836470033104875320381195918341077462494 * 10 ^ 70 +
        7006890161627451939303262213244787829884910543016567628856739136241621) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_72 :
    recurrence2Scalar2Left.coeff 72 =
      -((3479175121644930073083817451354372434724477866306854198607899 * 10 ^ 70 +
        8440730661392592156998172849147111629519053426586576071232040549374699) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_73 :
    recurrence2Scalar2Left.coeff 73 =
      ((37581083199818579932951535145082112560997198518984955363868341 * 10 ^ 70 +
        3135842940166160930645617645179666266495405033366329605005018039346269) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_74 :
    recurrence2Scalar2Left.coeff 74 =
      -((382671168490014286438332741066337464055393088613499199922192356 * 10 ^ 70 +
        0052695632843544571726519501883947879608959335497095092326604987275616) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_75 :
    recurrence2Scalar2Left.coeff 75 =
      ((3689293314953338549749233476236943540737999920754907149174391000 * 10 ^ 70 +
        5652803744371633007595532880322659766875795795520690360427920020142985) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_76 :
    recurrence2Scalar2Left.coeff 76 =
      -((33787744726819881861470323391918932813376164735479765111402259190 * 10 ^ 70 +
        3951747153520345710919521617696737641340944626635691747897874775980510) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_77 :
    recurrence2Scalar2Left.coeff 77 =
      ((294718355550947044365649171448470962218400154277982121469482365610 * 10 ^ 70 +
        5862784399547174058131343271717257203979630251653290339727674813814066) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_78 :
    recurrence2Scalar2Left.coeff 78 =
      -((2453574224273264227980320308939672591229613740406427661708332162111 * 10 ^ 70 +
        9802253314936304489815248633387137937033627244937369318838477632362764) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_79 :
    recurrence2Scalar2Left.coeff 79 =
      ((19528679628202398349780310163671838375911042301272797349851152125528 * 10 ^ 70 +
        0368616024564606895177990222949377138103894026544606830690088232826560) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_80 :
    recurrence2Scalar2Left.coeff 80 =
      -((148806932796755723596588006156871748258654598616870748760566736886845 * 10 ^ 70 +
        4470597434393683724323471812116677232268529584767795237198908959193275) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_81 :
    recurrence2Scalar2Left.coeff 81 =
      ((1086749884754588267393733176580871654477447487810520139641842261902556 * 10 ^ 70 +
        6789066874613138780541933870481231677293973268769732387311611293578596) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_82 :
    recurrence2Scalar2Left.coeff 82 =
      -((7613468073789463212192873414692256303447111512727455300665098088724754 * 10 ^ 70 +
        0026380284801347395283674542119956209448154298500390777818742332907693) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_83 :
    recurrence2Scalar2Left.coeff 83 =
      (((5 * 10 ^ 70 +
        1204314254865166213767475670857560016049845592631218497836263257857457) * 10 ^ 70 +
        8963039404408754870513019259418732526736557607136679556856779296324270) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_84 :
    recurrence2Scalar2Left.coeff 84 =
      -(((33 * 10 ^ 70 +
        0809102846814970458531257869101825766696471133678107865893511150200160) * 10 ^ 70 +
        1469141110699685743707856856152394922271466973756741382217758163495172) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_85 :
    recurrence2Scalar2Left.coeff 85 =
      (((205 * 10 ^ 70 +
        4134701132078945450769468969856347053385523967076581718842068114851468) * 10 ^ 70 +
        3040939777543560004135661035191913082716520267271874143563593967581020) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_86 :
    recurrence2Scalar2Left.coeff 86 =
      -(((1226 * 10 ^ 70 +
        4448521164850441036711001360900899102478852122772403678709465076444964) * 10 ^ 70 +
        7760621846758170593776374510055525627831382564310653560562761633846177) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_87 :
    recurrence2Scalar2Left.coeff 87 =
      (((7043 * 10 ^ 70 +
        0686814827633286085668130915197678885194282213635944034737495905423956) * 10 ^ 70 +
        2424121228167773522307692908591413659292254800585661362084809956876334) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_88 :
    recurrence2Scalar2Left.coeff 88 =
      -(((38906 * 10 ^ 70 +
        4757774210024060294068546807931011247091679588738824289497684143908854) * 10 ^ 70 +
        0074909911104934272253506009461529513462655188099653263136084198017728) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_89 :
    recurrence2Scalar2Left.coeff 89 =
      (((206724 * 10 ^ 70 +
        6267474681411197620082216357550361779121234218375808860204253443012199) * 10 ^ 70 +
        9165082750488335182018330827859403011854394396125624190932386979381121) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_90 :
    recurrence2Scalar2Left.coeff 90 =
      -(((1056207 * 10 ^ 70 +
        7680277299344252509559475940288934755160126920542564329852514144204152) * 10 ^ 70 +
        0096175803096461064779463780823033871160914630235252144801168008778758) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_91 :
    recurrence2Scalar2Left.coeff 91 =
      (((5186693 * 10 ^ 70 +
        8439748252386095895521287020526186398922323599257938781387137491764374) * 10 ^ 70 +
        4505343653105755097382058353461801537692683230136311783545705550583119) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_92 :
    recurrence2Scalar2Left.coeff 92 =
      -(((24464821 * 10 ^ 70 +
        6132300824182064683784861445028743484039200211795026279322788325707681) * 10 ^ 70 +
        9247822129104357842156346278935930756091528356209921963038231637336778) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_93 :
    recurrence2Scalar2Left.coeff 93 =
      (((110750537 * 10 ^ 70 +
        4995669635804239534296981406371286107366875798566907658045346855113144) * 10 ^ 70 +
        9961038416884765583141452005691749693937861754762286756775966311017216) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_94 :
    recurrence2Scalar2Left.coeff 94 =
      -(((480618954 * 10 ^ 70 +
        4187930798802087809635982444135270656968560902869196564171259162137220) * 10 ^ 70 +
        6174566730615133035107483511756973278118252330677627398312176458221574) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_95 :
    recurrence2Scalar2Left.coeff 95 =
      (((1995867994 * 10 ^ 70 +
        0840208892115475319013622326370805407553491351947249768036286983324307) * 10 ^ 70 +
        7689112499589817929270241077084499237235259541027655908562686125084557) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_96 :
    recurrence2Scalar2Left.coeff 96 =
      -(((7908057620 * 10 ^ 70 +
        5540486363738516240764921395181744783010647754621221727860199039553092) * 10 ^ 70 +
        0869870350454211197482112877424361627301460337982884906691874443523109) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_97 :
    recurrence2Scalar2Left.coeff 97 =
      (((29753391637 * 10 ^ 70 +
        9208967099318128650818189559640235414801776678576127776354989385551877) * 10 ^ 70 +
        6195738902538895848883022449654068233916569077860059210327873913635797) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_98 :
    recurrence2Scalar2Left.coeff 98 =
      -(((105486408693 * 10 ^ 70 +
        2920197326985262472210806823126484681852550358619061222431689618576429) * 10 ^ 70 +
        3943136503327418033177315439347098628016557348539220542693472902592476) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_99 :
    recurrence2Scalar2Left.coeff 99 =
      (((348109772068 * 10 ^ 70 +
        0646987760169022218681587676120995559056535529934714767638287019410791) * 10 ^ 70 +
        2669835253533309567857371731028383703159144750910044415363662242083572) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_100 :
    recurrence2Scalar2Left.coeff 100 =
      -(((1047388959452 * 10 ^ 70 +
        3055630043844087336680505867862132319865875767805601909475097568192790) * 10 ^ 70 +
        3431851935758510073060857296576852761961172693490102403278436093222549) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_101 :
    recurrence2Scalar2Left.coeff 101 =
      (((2759123793250 * 10 ^ 70 +
        4436006089038523505925148985959553812096876590694670963202441663407749) * 10 ^ 70 +
        0628203879068108087827573582239337744839225002103720888719262101308628) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_102 :
    recurrence2Scalar2Left.coeff 102 =
      -(((5711470699689 * 10 ^ 70 +
        5158524814152394345425984306369581810406162587924040042301374351188106) * 10 ^ 70 +
        0394851372440432662140215652624315386459180399768460869826228336819673) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_103 :
    recurrence2Scalar2Left.coeff 103 =
      (((4939439120261 * 10 ^ 70 +
        9214326135780747739736328897531505014302339485480813741884711227284589) * 10 ^ 70 +
        4183911130841754581632373643363411306133412278359290830920179140895469) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_104 :
    recurrence2Scalar2Left.coeff 104 =
      (((35049060282897 * 10 ^ 70 +
        2901016378588714825129821331176752722315325777710256676487647625038608) * 10 ^ 70 +
        7308906080731874383029978262060384437649980135216089853261286922892291) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_105 :
    recurrence2Scalar2Left.coeff 105 =
      -(((294628083892778 * 10 ^ 70 +
        6006164529103424179656909038303619906236925636469584085515981038333577) * 10 ^ 70 +
        2580695116794888719482095224986045507210826777996240641303292567170666) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_106 :
    recurrence2Scalar2Left.coeff 106 =
      (((1577523997002417 * 10 ^ 70 +
        9117567535738913962118180721964072162974932058298931315316106994591869) * 10 ^ 70 +
        3355470332640236053138468571821038117955276715918668349389258879251319) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_107 :
    recurrence2Scalar2Left.coeff 107 =
      -(((7146726586652096 * 10 ^ 70 +
        5678653428112982920323280855893833776989619865215998929346623405182403) * 10 ^ 70 +
        9631302511395179571262401985709145371607260371671471282905814246198465) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_108 :
    recurrence2Scalar2Left.coeff 108 =
      (((28783499981503978 * 10 ^ 70 +
        6061486868497233682523057676129888152826969463640896078788572449709904) * 10 ^ 70 +
        0738872766876882472301154626611621610389298905559873378853614077290511) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_109 :
    recurrence2Scalar2Left.coeff 109 =
      -(((101539121113156348 * 10 ^ 70 +
        7551868558879037525371044358408408385431791899266583882654767909788972) * 10 ^ 70 +
        7371097839370509223539173719557982337513715143044423376681893031554326) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar2Left_coeff_110 :
    recurrence2Scalar2Left.coeff 110 =
      (((295147199332691408 * 10 ^ 70 +
        6575454669281788409747840779553667543902256425917434202233117153526619) * 10 ^ 70 +
        9980086912351720366981592961184720245342316469841236934139682445478348) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

private theorem recurrence2Scalar2Left_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_111 :
    recurrence2Scalar2Left.coeff 111 =
      -(((603037210445030539 * 10 ^ 70 +
        8227675897735096385406038407284231872541427648185817486553350361090549) * 10 ^ 70 +
        1570479626503393551660407044313768720304062641578076550695770513256975) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 1 +
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
  rw [recurrence2Scalar2Left_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_112 :
    recurrence2Scalar2Left.coeff 112 =
      (((327214845053100867 * 10 ^ 70 +
        1580667912212795392157941570719431702306275607904707287058759273899971) * 10 ^ 70 +
        0609270008216939799828996486583890000795941047273016516240421730449547) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 2 +
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
  rw [recurrence2Scalar2Left_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_113 :
    recurrence2Scalar2Left.coeff 113 =
      (((2791505203595608298 * 10 ^ 70 +
        5528195553966971435825822525347589861253251093973111743621044911786202) * 10 ^ 70 +
        6788592377349290524621659500044288112934555299615143212147988331285603) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 3 +
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
  rw [recurrence2Scalar2Left_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_114 :
    recurrence2Scalar2Left.coeff 114 =
      -(((4660965901662127327 * 10 ^ 70 +
        8777928592814333301248571977023417480918390189081219233959475632516827) * 10 ^ 70 +
        8898011189322819150696292997825436835463339639547806066270346644658103) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 4 +
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
  rw [recurrence2Scalar2Left_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_115 :
    recurrence2Scalar2Left.coeff 115 =
      -(((69356656309833083646 * 10 ^ 70 +
        0826803773469910416112990821254987699794437632654296944374562513857922) * 10 ^ 70 +
        6390696744432411506557306054353767820589073038035436283524808636260083) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 5 +
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
  rw [recurrence2Scalar2Left_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_116 :
    recurrence2Scalar2Left.coeff 116 =
      (((591132049616009560185 * 10 ^ 70 +
        6590226633526149816552916329684546839585370209540193680058702546052107) * 10 ^ 70 +
        3784603046274956313558621377840132212035268893423044296023231626034381) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 6 +
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
  rw [recurrence2Scalar2Left_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_117 :
    recurrence2Scalar2Left.coeff 117 =
      -(((2385268315679782208304 * 10 ^ 70 +
        9619326207313067030350194096600439232876111796361525938364391242972826) * 10 ^ 70 +
        5653362794518184824257584791692427398496528370806349974059788756661638) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 7 +
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
  rw [recurrence2Scalar2Left_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_118 :
    recurrence2Scalar2Left.coeff 118 =
      (((3675673711831537910988 * 10 ^ 70 +
        3791040414879583335198097374498096964061972867794117835691204812487774) * 10 ^ 70 +
        3434106324657396082072659228927284180030034670691417330198418681004654) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 8 +
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
  rw [recurrence2Scalar2Left_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_119 :
    recurrence2Scalar2Left.coeff 119 =
      (((20387067810673547168849 * 10 ^ 70 +
        2220420644227886232639114249008983642245671186290737387161215869415913) * 10 ^ 70 +
        7861293374270301008539667309477790390209869211934343126684498483924420) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 9 +
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
  rw [recurrence2Scalar2Left_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_120 :
    recurrence2Scalar2Left.coeff 120 =
      -(((188948693330150072889785 * 10 ^ 70 +
        1392628616119334836411130944592224070753835678261221294291490240892257) * 10 ^ 70 +
        4704850616212331059073504804557281272072908562380980248039415156396368) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 10 +
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
  rw [recurrence2Scalar2Left_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_121 :
    recurrence2Scalar2Left.coeff 121 =
      (((819959092267795427192817 * 10 ^ 70 +
        9235292478001085304336694895261968060681278354681758661526348029911634) * 10 ^ 70 +
        2023394560513237542538648576152916041439527149873261022352306795300590) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 11 +
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
  rw [recurrence2Scalar2Left_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_122 :
    recurrence2Scalar2Left.coeff 122 =
      -(((2000008450998648168560548 * 10 ^ 70 +
        6581300383602922494153546917506757369613900102431661475936919386709525) * 10 ^ 70 +
        9195455862955669011682070767945545032174573412049912564592067282257073) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 12 +
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
  rw [recurrence2Scalar2Left_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_123 :
    recurrence2Scalar2Left.coeff 123 =
      -(((286508625990672102212959 * 10 ^ 70 +
        8793813994707414679390281830315290321806533839920546957429868227156841) * 10 ^ 70 +
        0344284976658183777352780190472584319004302064102064610814931895404806) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 13 +
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
  rw [recurrence2Scalar2Left_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_124 :
    recurrence2Scalar2Left.coeff 124 =
      (((29477000068265375264372521 * 10 ^ 70 +
        0937182434223207626460541791191179667919572250625278307341911154336151) * 10 ^ 70 +
        7250286497600628544817710693240273732534047600838729981873295385151395) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 14 +
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
  rw [recurrence2Scalar2Left_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_125 :
    recurrence2Scalar2Left.coeff 125 =
      -(((159436638158268716271420359 * 10 ^ 70 +
        5656698873865363659162885164590177463811342622338465201158674421820510) * 10 ^ 70 +
        2497885193493708807802537077890337017641258571705239226462225192590515) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 15 +
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
  rw [recurrence2Scalar2Left_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_126 :
    recurrence2Scalar2Left.coeff 126 =
      (((493727847568537859441292417 * 10 ^ 70 +
        7958873600993537205471979384721145814201773190332412507254403595179098) * 10 ^ 70 +
        0328195972880713348463279165809311186666230691125682409316924532132509) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 16 +
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
  rw [recurrence2Scalar2Left_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_127 :
    recurrence2Scalar2Left.coeff 127 =
      -(((804274598873378963028854377 * 10 ^ 70 +
        0909997052603731307768899730880621486042812572690308178093381035434539) * 10 ^ 70 +
        2838337364406448984081501525083507732603263662328557055134241370810749) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 17 +
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
  rw [recurrence2Scalar2Left_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_128 :
    recurrence2Scalar2Left.coeff 128 =
      -(((610417412017172978239604666 * 10 ^ 70 +
        6134059342812843007596453179919163718362284638473768392928946242953415) * 10 ^ 70 +
        5002779087565077849172843115592670902549381672359327471048817362041434) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 18 +
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
  rw [recurrence2Scalar2Left_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_129 :
    recurrence2Scalar2Left.coeff 129 =
      (((9970112345969774779205332378 * 10 ^ 70 +
        0427880742014842656109938676771765916157948240316682894036222050094118) * 10 ^ 70 +
        9242332488349824889947062339511606444365282033203281972743293407336589) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 19 +
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
  rw [recurrence2Scalar2Left_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_130 :
    recurrence2Scalar2Left.coeff 130 =
      -(((62167275467623010426248473771 * 10 ^ 70 +
        1202274939820260169652011961515732767701993362514596554388925258731775) * 10 ^ 70 +
        6096353495467994665822142847580782463560293006422070907282566680856615) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 20 +
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
  rw [recurrence2Scalar2Left_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_131 :
    recurrence2Scalar2Left.coeff 131 =
      (((390202708230716084851433544787 * 10 ^ 70 +
        8012708605404110295415912745530882881709475787491474040176882981134684) * 10 ^ 70 +
        4684516646374927399022830306504620954028037055958046274269966192522011) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 21 +
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
  rw [recurrence2Scalar2Left_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_132 :
    recurrence2Scalar2Left.coeff 132 =
      -(((1948607952975093306933102461500 * 10 ^ 70 +
        2937864640010854569433067082555523561831556975536007331949089967146097) * 10 ^ 70 +
        1584457896185144552164998392145693277881411611521433559135005813749721) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 22 +
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
  rw [recurrence2Scalar2Left_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_133 :
    recurrence2Scalar2Left.coeff 133 =
      (((5338129563563850753221627419211 * 10 ^ 70 +
        9705819205502101935653100792594129925882340132698988506543157209798291) * 10 ^ 70 +
        2083032858523910509815395626188073444106837653671710104420975584455814) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 23 +
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
  rw [recurrence2Scalar2Left_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_134 :
    recurrence2Scalar2Left.coeff 134 =
      (((6915140193779832442769052647651 * 10 ^ 70 +
        0028311585555640404353729164193514892793430160866001612064321551945990) * 10 ^ 70 +
        0913026241269676191034529579976316393581756031436065450096431847535802) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 24 +
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
  rw [recurrence2Scalar2Left_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_135 :
    recurrence2Scalar2Left.coeff 135 =
      -(((142406237510490359732166699053264 * 10 ^ 70 +
        3384186904319565676234206083806277749193503682252932792821996529565260) * 10 ^ 70 +
        5589932306325415316067291954743848663247857971235773587186820938829983) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 25 +
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
  rw [recurrence2Scalar2Left_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_136 :
    recurrence2Scalar2Left.coeff 136 =
      (((641575748012554940701639866672881 * 10 ^ 70 +
        5790810425655249490388209686558088162461313506021313593787508135914965) * 10 ^ 70 +
        7590401964461333625102557322189403394520187499622515570929911952328377) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 26 +
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
  rw [recurrence2Scalar2Left_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_137 :
    recurrence2Scalar2Left.coeff 137 =
      -(((943121543616786591393813185590696 * 10 ^ 70 +
        2201342167019073145014932844853658428846234407280807746675939210815219) * 10 ^ 70 +
        0075683049687187329430670233365665819226702251572103151537500912098620) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 27 +
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
  rw [recurrence2Scalar2Left_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_138 :
    recurrence2Scalar2Left.coeff 138 =
      -(((4755637732811673907958559254412108 * 10 ^ 70 +
        9697892379630623126233099901548506000017071830528037777169079188120417) * 10 ^ 70 +
        9036164980065071099619181968516041924510413315132771504871821626763213) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 28 +
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
  rw [recurrence2Scalar2Left_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_139 :
    recurrence2Scalar2Left.coeff 139 =
      (((31373410101635322863183060631842496 * 10 ^ 70 +
        8120012600902031883455110294726681325154926449630785075410883095521754) * 10 ^ 70 +
        1017870071978803278832513834338848301556075767353236041906971327667493) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 29 +
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
  rw [recurrence2Scalar2Left_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_140 :
    recurrence2Scalar2Left.coeff 140 =
      -(((56117131295889923502930875219832196 * 10 ^ 70 +
        6381979460124733977416949170232516870197983816163565399525607666054774) * 10 ^ 70 +
        0238440523107569280260552476502169614678774819515091626738967775126452) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 30 +
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
  rw [recurrence2Scalar2Left_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_141 :
    recurrence2Scalar2Left.coeff 141 =
      -(((198555272826095366479696891782858040 * 10 ^ 70 +
        0068489366005921229416792238521561484643754569744706359748244894485004) * 10 ^ 70 +
        8296443245048227937575866219921471982817683847045285603679664852006390) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 31 +
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
  rw [recurrence2Scalar2Left_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_142 :
    recurrence2Scalar2Left.coeff 142 =
      (((1377377562692175692561221473915166192 * 10 ^ 70 +
        8632652763232251234326377030118023676917135364430026864167351942242425) * 10 ^ 70 +
        4115661039536121228532264650646430320159761030850824244895647511752674) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 32 +
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
  rw [recurrence2Scalar2Left_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_143 :
    recurrence2Scalar2Left.coeff 143 =
      -(((1955264128165858640711612130657937225 * 10 ^ 70 +
        5520466555153254858174517115275788996897671860354858506105593400661382) * 10 ^ 70 +
        2351529906746694783423131813659959665684036431689525391355945379163171) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 33 +
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
  rw [recurrence2Scalar2Left_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_144 :
    recurrence2Scalar2Left.coeff 144 =
      -(((11794399837792569195182103219239828050 * 10 ^ 70 +
        2022741476255043946006869110175889433928867249001765580412292320881469) * 10 ^ 70 +
        8130553314381741414869994998296567025530426455799276934099503469667851) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 34 +
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
  rw [recurrence2Scalar2Left_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_145 :
    recurrence2Scalar2Left.coeff 145 =
      (((65927675241520560791099113513771365585 * 10 ^ 70 +
        4830320928968748700634397493504159649689330242703171766657704022143289) * 10 ^ 70 +
        3718034937433184322539404594414728750315543523349494840493048832321298) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 35 +
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
  rw [recurrence2Scalar2Left_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_146 :
    recurrence2Scalar2Left.coeff 146 =
      -(((70190760132429631002595692590693494943 * 10 ^ 70 +
        6929333638671330170847411382633867821771517935082946232335901066216543) * 10 ^ 70 +
        0610537560688827354477902863372711025315839008659893971683845566867512) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 36 +
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
  rw [recurrence2Scalar2Left_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_147 :
    recurrence2Scalar2Left.coeff 147 =
      -(((594222424915232254748840503720591659392 * 10 ^ 70 +
        1570942055319156601483447572701577226379420429939008227796579455705159) * 10 ^ 70 +
        2174350801367495714856624221540563705188251005924176961400950791957119) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 37 +
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
  rw [recurrence2Scalar2Left_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_148 :
    recurrence2Scalar2Left.coeff 148 =
      (((2731514562523465416778279832758861230596 * 10 ^ 70 +
        9681876736225416110718444286423547384168086807853077693252911201781993) * 10 ^ 70 +
        8852545362131323154852520966923129155346550299239666424749534227627085) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 38 +
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
  rw [recurrence2Scalar2Left_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_149 :
    recurrence2Scalar2Left.coeff 149 =
      -(((953156868689262796082104090081851528606 * 10 ^ 70 +
        4667997754225929834435764410259071043970505180307536143510385271935823) * 10 ^ 70 +
        1980966674003856132366603619793728751121083005209638262882745332883329) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 39 +
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
  rw [recurrence2Scalar2Left_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_150 :
    recurrence2Scalar2Left.coeff 150 =
      -(((31981106473544408150550006266019016953404 * 10 ^ 70 +
        1690801012141992921660778097270749559853991423552977269060237330554375) * 10 ^ 70 +
        0004193381779932200414790917902343771514504174820764609893383936946096) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 151 = 40 +
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
  rw [recurrence2Scalar2Left_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_151 :
    recurrence2Scalar2Left.coeff 151 =
      (((110905396567926465917869989138484369678436 * 10 ^ 70 +
        4887110675216515866636847575815317264259685645419782833845917346214002) * 10 ^ 70 +
        3785062574258363653566923261086378044498483761740477962762550207539326) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 152 = 41 +
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
  rw [recurrence2Scalar2Left_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_152 :
    recurrence2Scalar2Left.coeff 152 =
      (((87202347688568147536747366338709281529946 * 10 ^ 70 +
        9059861946091043230675149463507352594828383660600089483124298536636330) * 10 ^ 70 +
        8134152720467227119871676811627236261521438122460068625445527903902785) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 153 = 42 +
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
  rw [recurrence2Scalar2Left_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_153 :
    recurrence2Scalar2Left.coeff 153 =
      -(((1885647683223483516504714523116973756703126 * 10 ^ 70 +
        0182194285125593925092962261471374229719695627601173741506428660946288) * 10 ^ 70 +
        2668568164521463465414206412756621680199251607000298703338276971108407) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 43 +
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
  rw [recurrence2Scalar2Left_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_154 :
    recurrence2Scalar2Left.coeff 154 =
      (((5607355020018830949086246488503991494840511 * 10 ^ 70 +
        7610019046382955785573453124239967762082521385496353186884034590504356) * 10 ^ 70 +
        4073005346714398301112514500618488966552469798029205134971137005278973) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 44 +
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
  rw [recurrence2Scalar2Left_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_155 :
    recurrence2Scalar2Left.coeff 155 =
      (((5418938120094153028642542586981246022731497 * 10 ^ 70 +
        2188358481321766987751404826964821329896917546821308106349885769786288) * 10 ^ 70 +
        9198759553055836677011852398608374264394008200436030247368358112120943) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 45 +
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
  rw [recurrence2Scalar2Left_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_156 :
    recurrence2Scalar2Left.coeff 156 =
      -(((98030985934313753901188341541746575066809597 * 10 ^ 70 +
        1253889738490251115035697987303516242314440752368004593430242298145796) * 10 ^ 70 +
        7704241580327418851056441148054229837902295875260802009802899452768182) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 46 +
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
  rw [recurrence2Scalar2Left_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_157 :
    recurrence2Scalar2Left.coeff 157 =
      (((311371738636520531362666469624846219195754944 * 10 ^ 70 +
        2006432369402699771458348479445267850589954052525655473315108688589276) * 10 ^ 70 +
        8491160425298406866889485307768029157085419804049000823024369756325916) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 47 +
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
  rw [recurrence2Scalar2Left_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_158 :
    recurrence2Scalar2Left.coeff 158 =
      (((41526280824016409669534356658193706744148015 * 10 ^ 70 +
        4584299147207909486086142365154754897518768880779501787891268719398101) * 10 ^ 70 +
        0634575259291389450453178374674345724870486362776717468061940818846346) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 48 +
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
  rw [recurrence2Scalar2Left_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_159 :
    recurrence2Scalar2Left.coeff 159 =
      -(((4063685872183626914798392201056537914348394193 * 10 ^ 70 +
        3126742767900938546552350143317842744792448354825373592947686701649589) * 10 ^ 70 +
        4728144261832349857784169955532403478384942426216891547282133484564518) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 49 +
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
  rw [recurrence2Scalar2Left_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_160 :
    recurrence2Scalar2Left.coeff 160 =
      (((15490057036555114166356904783244404205283149692 * 10 ^ 70 +
        6300539794452947637686360189285444336017903431248765134579017475674330) * 10 ^ 70 +
        9828845637272489110672450338527246545945806784456451097400784701347583) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 50 +
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
  rw [recurrence2Scalar2Left_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_161 :
    recurrence2Scalar2Left.coeff 161 =
      -(((12869366777976457448687792495610624843831074988 * 10 ^ 70 +
        0173556532658843422826198126072342224546331921665140851838639214886294) * 10 ^ 70 +
        5231451959156461398048512440966938508514840689646844038975115984319723) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 51 +
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
  rw [recurrence2Scalar2Left_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_162 :
    recurrence2Scalar2Left.coeff 162 =
      -(((127047124722664001108194900480663830014161673335 * 10 ^ 70 +
        5693556278035965054119154512509005878029970156158569220586198360847675) * 10 ^ 70 +
        1333258549218327955872795152569352943602437667927568958249834498303554) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 52 +
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
  rw [recurrence2Scalar2Left_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_163 :
    recurrence2Scalar2Left.coeff 163 =
      (((635725806173754211393327587299047198969417520794 * 10 ^ 70 +
        9499969975875136354624525917416265114137956176513357747876912699630739) * 10 ^ 70 +
        0046924312877611404562820708323968618521199987500904271169365323363862) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 53 +
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
  rw [recurrence2Scalar2Left_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_164 :
    recurrence2Scalar2Left.coeff 164 =
      -(((1069338406764983241201863288870632146978845534435 * 10 ^ 70 +
        1619693264882698997588882678194499769539030502931655499339296855378014) * 10 ^ 70 +
        7806110463276867283387630623605356841804021994043157866019500705021688) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 54 +
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
  rw [recurrence2Scalar2Left_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_165 :
    recurrence2Scalar2Left.coeff 165 =
      -(((2648142837513308471859014318744850996239670746025 * 10 ^ 70 +
        5317811366222418182313137963021195034344873710768300039049058624375277) * 10 ^ 70 +
        2709307262658908296516566054057899799905834691721179239886368304291840) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 55 +
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
  rw [recurrence2Scalar2Left_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_166 :
    recurrence2Scalar2Left.coeff 166 =
      (((21178659047174245962126335195184745846157810705217 * 10 ^ 70 +
        3400105412225348681900811615804179041831956673751332335982033983511470) * 10 ^ 70 +
        8866222980513482009516800030067126744192435403051359869450838659512823) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 56 +
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
  rw [recurrence2Scalar2Left_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_167 :
    recurrence2Scalar2Left.coeff 167 =
      -(((53262636427985257820777234542267040621819883593834 * 10 ^ 70 +
        4179685984253647943511296300617582773310363024504674112340558134215412) * 10 ^ 70 +
        3570329662258148249789532853130662821235238848142963609284007349317488) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 57 +
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
  rw [recurrence2Scalar2Left_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_168 :
    recurrence2Scalar2Left.coeff 168 =
      -(((10908911221474547840679428129967974831789267937515 * 10 ^ 70 +
        4419980603463922600044028698233586682749302102087289894200229901954918) * 10 ^ 70 +
        2329470928816754624471416622625794280389753930687870205096532194080394) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 58 +
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
  rw [recurrence2Scalar2Left_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_169 :
    recurrence2Scalar2Left.coeff 169 =
      (((566065971867870058159558861420521828632026756108209 * 10 ^ 70 +
        4970774734869227218156587753501024651079963803951552941259963250716189) * 10 ^ 70 +
        7844689737928743857670024090593535213982080373026074422940337163878200) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 59 +
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
  rw [recurrence2Scalar2Left_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_170 :
    recurrence2Scalar2Left.coeff 170 =
      -(((2025766800204495354544381384765802086214733700965148 * 10 ^ 70 +
        5345779810110160880909417560195564966900761089420296982817273951186108) * 10 ^ 70 +
        7799443199499860536340346320236367097488823487629288205256496062031921) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 60 +
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
  rw [recurrence2Scalar2Left_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_171 :
    recurrence2Scalar2Left.coeff 171 =
      (((2206781942362885174590826719477851851253046450425441 * 10 ^ 70 +
        9424131749759565584243542539128576093089238785667984324575920940911509) * 10 ^ 70 +
        9663149897831534906282042283278425806335221964932922155093846519303454) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 61 +
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
  rw [recurrence2Scalar2Left_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_172 :
    recurrence2Scalar2Left.coeff 172 =
      (((10847248708218683342484777207780305272007077477502230 * 10 ^ 70 +
        1753296221968756802281438752004925241897696713875792323060720064199230) * 10 ^ 70 +
        1787700728196211535978792093098805901695698560839997582541099255159401) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 62 +
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
  rw [recurrence2Scalar2Left_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_173 :
    recurrence2Scalar2Left.coeff 173 =
      -(((61730162546794158370561143938710363461386684700934370 * 10 ^ 70 +
        4921855213082151333187117334387535568002445778691909499264915686170524) * 10 ^ 70 +
        6944196445402067331235066070140593829339003235809694976273041351619228) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 63 +
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
  rw [recurrence2Scalar2Left_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_174 :
    recurrence2Scalar2Left.coeff 174 =
      (((134648756847694839433399723690010917198304038548336808 * 10 ^ 70 +
        6654561572765296737251108283940612149331641536987958425960017362510993) * 10 ^ 70 +
        2459621370680426615980018216508823639078534304549256954981497210031826) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 64 +
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
  rw [recurrence2Scalar2Left_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_175 :
    recurrence2Scalar2Left.coeff 175 =
      (((47593446914886227851881505498771724902057357449459047 * 10 ^ 70 +
        9008274496429978103490964053107334659952365771664624171948395175491777) * 10 ^ 70 +
        1779266938591457907107840237368670044466039216979947342761956806078768) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 65 +
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
  rw [recurrence2Scalar2Left_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_176 :
    recurrence2Scalar2Left.coeff 176 =
      -(((1388216938664807203917524014559693685582444739861163133 * 10 ^ 70 +
        0063966473791131138725682865582818990070284889395354354133696647416899) * 10 ^ 70 +
        8117431346423845164298735683240858529772468070657531749832678993904603) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 66 +
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
  rw [recurrence2Scalar2Left_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_177 :
    recurrence2Scalar2Left.coeff 177 =
      (((4910066166086968267612027543666267911115721324164787196 * 10 ^ 70 +
        1308028607681397754710781127530257962900258982208431594783301116032039) * 10 ^ 70 +
        8471971431904373028882881965590119709945129718581049296024414879563487) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 67 +
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
  rw [recurrence2Scalar2Left_coeff_177_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_178 :
    recurrence2Scalar2Left.coeff 178 =
      -(((6863516558401828582284673644742371801909665726726595858 * 10 ^ 70 +
        2905541143222839522740739408635278949046437488807463986424106407036603) * 10 ^ 70 +
        6112919327407147044934736342440067824109199405035856024108653401496381) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 68 +
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
  rw [recurrence2Scalar2Left_coeff_178_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_179 :
    recurrence2Scalar2Left.coeff 179 =
      -(((15353389551891325768296696814951029614265430583693616522 * 10 ^ 70 +
        3138454749523930217230703386626333628037126953510727269663174502855031) * 10 ^ 70 +
        8304176510337568025645906944069989850699681241191320424386908324878193) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 69 +
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
  rw [recurrence2Scalar2Left_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_180 :
    recurrence2Scalar2Left.coeff 180 =
      (((116645720734528903986506375626545131311181122789546362174 * 10 ^ 70 +
        8868987757390914286701852515669590501556385033622686897170071820074272) * 10 ^ 70 +
        4258862364371701456720295200619148579624978610004903823358600531806849) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 70 +
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
  rw [recurrence2Scalar2Left_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_181 :
    recurrence2Scalar2Left.coeff 181 =
      -(((324362221101189110067618324605615346533181686311445433000 * 10 ^ 70 +
        3030349440780183018720569011725711601138428903057441562680795700456748) * 10 ^ 70 +
        3998036648439774889125729727455060375260787790169034066195185709407066) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 71 +
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
  rw [recurrence2Scalar2Left_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_182 :
    recurrence2Scalar2Left.coeff 182 =
      (((312494953755837722743190013236774762818237031977309036776 * 10 ^ 70 +
        6358099405083535829773128590864195478445672903886924116121253030691249) * 10 ^ 70 +
        8081197731362498517951778435442550123231102234247778313275270158669343) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 72 +
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
  rw [recurrence2Scalar2Left_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_183 :
    recurrence2Scalar2Left.coeff 183 =
      (((1361198100290975601336192465039167769008297888602019266108 * 10 ^ 70 +
        4317184565461902227816703172478452588982098028255236843129760704253657) * 10 ^ 70 +
        9619179386306469967841583729216480083187704993337349874582024188530437) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 73 +
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
  rw [recurrence2Scalar2Left_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_184 :
    recurrence2Scalar2Left.coeff 184 =
      -(((7692874454502926268648460984526669634066062139571950745211 * 10 ^ 70 +
        4652421503625029872382622631261665927938257570510903253225897197778974) * 10 ^ 70 +
        7543231560588891588393011476459169427913209095243969199560941730731248) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 74 +
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
  rw [recurrence2Scalar2Left_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_185 :
    recurrence2Scalar2Left.coeff 185 =
      (((19343089727956890748044390026017571662215806762156391362711 * 10 ^ 70 +
        0998168353787674801028395985159879915052604578779111113416587171856697) * 10 ^ 70 +
        8743258813037350025110319158828333640681964420340843799180163245918851) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 75 +
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
  rw [recurrence2Scalar2Left_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_186 :
    recurrence2Scalar2Left.coeff 186 =
      -(((17048126872111611135639187575193203953210040595856871167921 * 10 ^ 70 +
        8864125556659534419628899887136124391695793540730063368308798324330253) * 10 ^ 70 +
        1213102101189271186713496274316414481769823689850936409560578828756608) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 76 +
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
  rw [recurrence2Scalar2Left_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_187 :
    recurrence2Scalar2Left.coeff 187 =
      -(((76791793144827385082482325427987731305726418936331115860892 * 10 ^ 70 +
        1782703393062683509823077934100953331923987056341703053915843163974518) * 10 ^ 70 +
        4593210509126481037882613134983139049333570089224690203292009570430708) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 77 +
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
  rw [recurrence2Scalar2Left_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_188 :
    recurrence2Scalar2Left.coeff 188 =
      (((421030363238423056520192766554587130075214632351462289436165 * 10 ^ 70 +
        3252336589113933178534256770894235383545425071783490326542758947612865) * 10 ^ 70 +
        4464704038359863552483044490608657127489109626387100262207040159807937) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 78 +
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
  rw [recurrence2Scalar2Left_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_189 :
    recurrence2Scalar2Left.coeff 189 =
      -(((1083885563763864598375234377965080853781755834477934988463523 * 10 ^ 70 +
        0607795464334666032977121235600631847078456401629412080305723889829822) * 10 ^ 70 +
        8496964838063060046155275188911343594258930734768161006839600324298114) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 79 +
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
  rw [recurrence2Scalar2Left_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_190 :
    recurrence2Scalar2Left.coeff 190 =
      (((1252633719980669760282330992626439267973457824210331589009407 * 10 ^ 70 +
        9183803746016012636798607474497736423893836898083973541799023665862092) * 10 ^ 70 +
        4085560973121810034592439586991416358290147666083009072846982764304621) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 80 +
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
  rw [recurrence2Scalar2Left_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_191 :
    recurrence2Scalar2Left.coeff 191 =
      (((2601359834960894035565276555476515713928468358675834409047427 * 10 ^ 70 +
        0912369717462264701881298476524930071490299840989902997421260742042486) * 10 ^ 70 +
        1396660965184017312185788367385850922773114722874570944561204355921429) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 81 +
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
  rw [recurrence2Scalar2Left_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_192 :
    recurrence2Scalar2Left.coeff 192 =
      -(((18565411944268601602757903882721704691645909496456403508194554 * 10 ^ 70 +
        7029842426191404646154640810219934730523186722618274507735069787277171) * 10 ^ 70 +
        0255409033483849698554838097056974699785633379180246673222157191896075) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 82 +
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
  rw [recurrence2Scalar2Left_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_193 :
    recurrence2Scalar2Left.coeff 193 =
      (((54803225669087922040438778697769503315782611918062783560595364 * 10 ^ 70 +
        3672748000505227634071078213156588378272291956164150642249760481043809) * 10 ^ 70 +
        3093042402627709093826712071502696597563199568362565133607893531911169) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 83 +
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
  rw [recurrence2Scalar2Left_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_194 :
    recurrence2Scalar2Left.coeff 194 =
      -(((91758650994382413851970728638935845536679403059823944657171214 * 10 ^ 70 +
        9276381712652122151778096129877185037154365715796827048690471455998436) * 10 ^ 70 +
        0905504311875110434361948474728718824044949416280000377009646691471503) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 84 +
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
  rw [recurrence2Scalar2Left_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_195 :
    recurrence2Scalar2Left.coeff 195 =
      (((5525790677238454404954722157159567056492259710539258405293571 * 10 ^ 70 +
        3655214574417118595125703496243916964450194370353736022879380004794086) * 10 ^ 70 +
        9001319457885028494744294196954852083165543443011020756982519175167692) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 85 +
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
  rw [recurrence2Scalar2Left_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_196 :
    recurrence2Scalar2Left.coeff 196 =
      (((555223852264301364903366439794694036554139875814762701280009940 * 10 ^ 70 +
        4189079727197329649556086258229034427462888952001871340526534345113925) * 10 ^ 70 +
        5985601275870217378544942263814877040604958969319552696903916477212285) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 86 +
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
  rw [recurrence2Scalar2Left_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_197 :
    recurrence2Scalar2Left.coeff 197 =
      -(((2190703120644147327005902276367318511211619171711784373130009419 * 10 ^ 70 +
        1084706068080730338802814599578107613514998536441552796655608014746940) * 10 ^ 70 +
        1139725463195743361239588309799940816180074710837686891310215803800883) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 87 +
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
  rw [recurrence2Scalar2Left_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_198 :
    recurrence2Scalar2Left.coeff 198 =
      (((5147414691307532885617922078426242099062724227779087816724451415 * 10 ^ 70 +
        1824165698063501543665824334107584493533639503840346080899079572952809) * 10 ^ 70 +
        8255684892000541539411475848970235749283790333437522144725477722690272) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 88 +
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
  rw [recurrence2Scalar2Left_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_199 :
    recurrence2Scalar2Left.coeff 199 =
      -(((6977458782192972728347503368990829768525319310899229194171085701 * 10 ^ 70 +
        3093992032618176580401779965233023349768315440384430392490151726213715) * 10 ^ 70 +
        0004331034304070320296242938360359136187180405299375435910018728861032) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 89 +
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
  rw [recurrence2Scalar2Left_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_200 :
    recurrence2Scalar2Left.coeff 200 =
      -(((2898628754885016642366911644393164045361804908815472606616914466 * 10 ^ 70 +
        9333306191651858923502105143973446795583743250286049723736635345623139) * 10 ^ 70 +
        8299497426278274509847283301530331225383833339743889900347668020367114) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 90 +
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
  rw [recurrence2Scalar2Left_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_201 :
    recurrence2Scalar2Left.coeff 201 =
      (((51097924131711445566949807537771669114589844091892564356373501690 * 10 ^ 70 +
        7639931140607431079286532637206057613448252191262189591865691511214301) * 10 ^ 70 +
        1627249296618010979074810161436551059989126642451362400675546910197214) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 91 +
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
  rw [recurrence2Scalar2Left_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_202 :
    recurrence2Scalar2Left.coeff 202 =
      -(((181893344063331811699880536232615189068416232145608203570697630694 * 10 ^ 70 +
        4225267478677348250149395991531704279282896284517683076429396798153508) * 10 ^ 70 +
        9877711193562876880708004974832070491405835156499060947844504032438491) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 92 +
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
  rw [recurrence2Scalar2Left_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_203 :
    recurrence2Scalar2Left.coeff 203 =
      (((424347077915538285935850384989397233318104177014299054011287457008 * 10 ^ 70 +
        5241225705704989874477378070010474861603931732783636655721965331951454) * 10 ^ 70 +
        5289556280152740168946546608304436597758715060399983997279476259180624) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 93 +
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
  rw [recurrence2Scalar2Left_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_204 :
    recurrence2Scalar2Left.coeff 204 =
      -(((664836516616577662539826691871877725678431141413549322303663689132 * 10 ^ 70 +
        4872788137811815211323855666741719723617796861786479109243650144990948) * 10 ^ 70 +
        6741170340160894563321140678269322821172579746630284712241946777856019) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 94 +
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
  rw [recurrence2Scalar2Left_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_205 :
    recurrence2Scalar2Left.coeff 205 =
      (((337058128217924885483721210535085278605579275973561891670636686458 * 10 ^ 70 +
        6748966092163764056585803742042999066970477435740621861671843369449295) * 10 ^ 70 +
        0914972162086598680351608900068586983119203309993430140606713030258304) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 95 +
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
  rw [recurrence2Scalar2Left_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_206 :
    recurrence2Scalar2Left.coeff 206 =
      (((2123026234303927352759508653358507312339641692086479590622682059716 * 10 ^ 70 +
        7252284687900474265226622904871235083359058766150961101094792723028692) * 10 ^ 70 +
        9178642701279145111519057365624721292380657810585844858924677415289679) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 96 +
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
  rw [recurrence2Scalar2Left_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_207 :
    recurrence2Scalar2Left.coeff 207 =
      -(((9880428880730925352224428025641010855720819890663902187132057599150 * 10 ^ 70 +
        9737932061298658270702993144173916294219159825872314436681553266589996) * 10 ^ 70 +
        6547280319240407013157223210583774371444225585399036111088030602598347) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 97 +
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
  rw [recurrence2Scalar2Left_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_208 :
    recurrence2Scalar2Left.coeff 208 =
      (((27548941658919795484766992188427575301666706950703536690146211983882 * 10 ^ 70 +
        0219554465359382437827663410826480135232652425432663985252844385942554) * 10 ^ 70 +
        9758481943720287173346533205095710888464398062384291529834912932941646) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 98 +
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
  rw [recurrence2Scalar2Left_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_209 :
    recurrence2Scalar2Left.coeff 209 =
      -(((58185458826324368548684690022676179426246195393216481564254682796439 * 10 ^ 70 +
        2445092393480140947535470708664679906204102083633846702271472932553003) * 10 ^ 70 +
        9145905999929403295080189627410438670069203243684131824987236482782023) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 99 +
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
  rw [recurrence2Scalar2Left_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_210 :
    recurrence2Scalar2Left.coeff 210 =
      (((93317754522990359827336921298257567556509715644826790414777144571300 * 10 ^ 70 +
        5905582248193069066254876908370778364451249069582063111857812468661932) * 10 ^ 70 +
        5184423491520223100029498725754508706057383380467122366351191552592315) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 100 +
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
  rw [recurrence2Scalar2Left_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_211 :
    recurrence2Scalar2Left.coeff 211 =
      -(((89577553968500354540542648532051162340485477460567016580643834442868 * 10 ^ 70 +
        9008845118519311126245783018595934967004538124307742206002500424030901) * 10 ^ 70 +
        4993243673199038397317339737698165380581140710369275259462330310671605) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 101 +
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
  rw [recurrence2Scalar2Left_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_212 :
    recurrence2Scalar2Left.coeff 212 =
      -(((75680435902013736665091813891405743322492613329469526763296446921286 * 10 ^ 70 +
        6280804131415209854593015131249726255848162934472634535976868775275470) * 10 ^ 70 +
        2169505215809405998973835158882807311761804701661997271718899707921826) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 102 +
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
  rw [recurrence2Scalar2Left_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_213 :
    recurrence2Scalar2Left.coeff 213 =
      (((674658514920351674603570582190202736369572719333852803284244806914765 * 10 ^ 70 +
        0748007253941055308676529695948894754369350438972773221103141864732895) * 10 ^ 70 +
        0829224957242025209218160903583397355519995267351807564577383131438848) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 103 +
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
  rw [recurrence2Scalar2Left_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_214 :
    recurrence2Scalar2Left.coeff 214 =
      -(((2219484412401583801548039240585648538114220600666675715670142799737767 * 10 ^ 70 +
        5951408759551591304044135941408110712837120699181812319229394237057111) * 10 ^ 70 +
        7495947863957759651896867727579486174311366030309274251547388682828098) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 104 +
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
  rw [recurrence2Scalar2Left_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_215 :
    recurrence2Scalar2Left.coeff 215 =
      (((5544153222839494110779847547238510453570504485546778664485365471092768 * 10 ^ 70 +
        5769485380367959919477405679939664244659967190258822204156728619790501) * 10 ^ 70 +
        6381692072320374966068697199139707102548175650967223192880259400470503) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 105 +
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
  rw [recurrence2Scalar2Left_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_216 :
    recurrence2Scalar2Left.coeff 216 =
      -((((1 * 10 ^ 70 +
        1813433047461844345429590447525820415437303437648850493341557390211774) * 10 ^ 70 +
        6304343126335043588830865014701541325694260179418385254163115696640400) * 10 ^ 70 +
        9771455655184633610355447222439899039856980996228960737062765654429133) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 106 +
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
  rw [recurrence2Scalar2Left_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_217 :
    recurrence2Scalar2Left.coeff 217 =
      ((((2 * 10 ^ 70 +
        2349787457950717034463068690129776166927252868566710539515794452372571) * 10 ^ 70 +
        9185986724217578727322635949313192075368235070883977942005902484542574) * 10 ^ 70 +
        7695964684617997685165492725262476603942524322634556695784353976610500) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 107 +
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
  rw [recurrence2Scalar2Left_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_218 :
    recurrence2Scalar2Left.coeff 218 =
      -((((3 * 10 ^ 70 +
        8132148053144114184338998574873997876645038397903163077210819643025267) * 10 ^ 70 +
        2431601317354125537830958570724702715828408286199127646942373912707792) * 10 ^ 70 +
        7233076385368719210160207626281684025547723549481272676784281695506994) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 108 +
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
  rw [recurrence2Scalar2Left_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_219 :
    recurrence2Scalar2Left.coeff 219 =
      ((((5 * 10 ^ 70 +
        8816788731533780724059542519638842055462297758077176282490268859533820) * 10 ^ 70 +
        3063431750151011732976268803381044847347782537947715416184660893295184) * 10 ^ 70 +
        8013475818000339241673434186874998239353329319173229816957094818166868) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 109 +
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
  rw [recurrence2Scalar2Left_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_220 :
    recurrence2Scalar2Left.coeff 220 =
      -((((8 * 10 ^ 70 +
        1193487211467436167892974827175864821793390723275529097643689603268056) * 10 ^ 70 +
        8083050718727734824361076850325298883613948307496826917680094753300368) * 10 ^ 70 +
        3571088798756508511626872865198417512081416395825466977108498576871936) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 110 +
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
  rw [recurrence2Scalar2Left_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_221 :
    recurrence2Scalar2Left.coeff 221 =
      ((((9 * 10 ^ 70 +
        7146392363197202901798795312178158680069723127317269798229709720827526) * 10 ^ 70 +
        5392399240473155185022757894079617205895723089141339904520262870759031) * 10 ^ 70 +
        8116115690294654146434725873883981170690054135649325039749425969331581) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 111 +
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
  rw [recurrence2Scalar2Left_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_222 :
    recurrence2Scalar2Left.coeff 222 =
      -((((9 * 10 ^ 70 +
        1440495936954417433500209057878506081500468122815741422949972709329131) * 10 ^ 70 +
        5368965657798752546847919531907149756953641192733170892892923646258868) * 10 ^ 70 +
        9351191611495873069658549931951742184520291300283990262815813298330403) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 112 +
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
  rw [recurrence2Scalar2Left_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_223 :
    recurrence2Scalar2Left.coeff 223 =
      ((((3 * 10 ^ 70 +
        9959519264575106695104627166764902079509556938081873591121605554559305) * 10 ^ 70 +
        0083135856002072709115725120575919293396119741043152278619173550263506) * 10 ^ 70 +
        9346391540391387368002843343955010426543623460777776849082282089894330) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 113 +
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
  rw [recurrence2Scalar2Left_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_224 :
    recurrence2Scalar2Left.coeff 224 =
      ((((9 * 10 ^ 70 +
        0714975477356887676301424866210539949165338696757803024349190918210703) * 10 ^ 70 +
        8141326805205784452046367268289626643634047150331756524233648646458763) * 10 ^ 70 +
        8933589773963504325543711425401873361466204948028125704225489673325111) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 114 +
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
  rw [recurrence2Scalar2Left_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_225 :
    recurrence2Scalar2Left.coeff 225 =
      -((((34 * 10 ^ 70 +
        1404758193184122363254194868322103523138077312905664856451756177769133) * 10 ^ 70 +
        5893994791258703532682216093064232966421259364747818550319502148773052) * 10 ^ 70 +
        9808907804474107581427647511177582605596517829428541002423287501938282) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 115 +
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
  rw [recurrence2Scalar2Left_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_226 :
    recurrence2Scalar2Left.coeff 226 =
      ((((75 * 10 ^ 70 +
        5359525086699658238091660860526474009143055872600690683618061936821164) * 10 ^ 70 +
        9340529105506086023403274820876897164592819022668221303005946721710904) * 10 ^ 70 +
        1688575036073648728011219956688561820063620639898568803214374080801730) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 116 +
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
  rw [recurrence2Scalar2Left_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_227 :
    recurrence2Scalar2Left.coeff 227 =
      -((((137 * 10 ^ 70 +
        0054856523478242766962984994213619199854564434244658511595967586903225) * 10 ^ 70 +
        2373338681436806791425410668107611302183580389991873500461532387102947) * 10 ^ 70 +
        7764959255949313348497794493769075835216904872154330376410499128962355) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 117 +
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
  rw [recurrence2Scalar2Left_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_228 :
    recurrence2Scalar2Left.coeff 228 =
      ((((220 * 10 ^ 70 +
        6558149713177888917574086087838209471504703065755017311278155347966816) * 10 ^ 70 +
        3105805968034382444311487042498758325384617491707763563980329329410990) * 10 ^ 70 +
        9259059706923259646248970649675133279394602050094776157919928471318615) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 118 +
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
  rw [recurrence2Scalar2Left_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_229 :
    recurrence2Scalar2Left.coeff 229 =
      -((((325 * 10 ^ 70 +
        8336557734872387748048529270929643139291011300824764628506962460781970) * 10 ^ 70 +
        8274087161481791830378859741712472435689839782664735760602701693031514) * 10 ^ 70 +
        1545166593298915405726925213652467253145347716184060445813693567540816) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 119 +
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
  rw [recurrence2Scalar2Left_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_230 :
    recurrence2Scalar2Left.coeff 230 =
      ((((448 * 10 ^ 70 +
        2258979594480589882697408762263130972355202942165778514417091762125736) * 10 ^ 70 +
        1775995259363731892457704629139618245711157101277645307252622052659651) * 10 ^ 70 +
        7895909202865186133151505820118216994731000171440836630702088905286381) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 120 +
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
  rw [recurrence2Scalar2Left_coeff_230_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_231 :
    recurrence2Scalar2Left.coeff 231 =
      -((((579 * 10 ^ 70 +
        4841353490530810299539581995174919776368324860825032974829508888922945) * 10 ^ 70 +
        9004830771817012263715626872867342532532697222496150211957025956460230) * 10 ^ 70 +
        7636256573674859858211448965556909893530682378817556084778798397248716) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 121 +
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
  rw [recurrence2Scalar2Left_coeff_231_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
