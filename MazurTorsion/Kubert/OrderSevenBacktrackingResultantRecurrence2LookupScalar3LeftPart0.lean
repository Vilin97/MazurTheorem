/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA3
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Left coefficient convolution

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
  recurrence2A3_coeff_0
  recurrence2A3_coeff_1
  recurrence2A3_coeff_2
  recurrence2A3_coeff_3
  recurrence2A3_coeff_4
  recurrence2A3_coeff_5
  recurrence2A3_coeff_6
  recurrence2A3_coeff_7
  recurrence2A3_coeff_8
  recurrence2A3_coeff_9
  recurrence2A3_coeff_10
  recurrence2A3_coeff_11
  recurrence2A3_coeff_12
  recurrence2A3_coeff_13
  recurrence2A3_coeff_14
  recurrence2A3_coeff_15
  recurrence2A3_coeff_16
  recurrence2A3_coeff_17
  recurrence2A3_coeff_18
  recurrence2A3_coeff_19
  recurrence2A3_coeff_20
  recurrence2A3_coeff_21
  recurrence2A3_coeff_22
  recurrence2A3_coeff_23
  recurrence2A3_coeff_24
  recurrence2A3_coeff_25
  recurrence2A3_coeff_26
  recurrence2A3_coeff_27
  recurrence2A3_coeff_28
  recurrence2A3_coeff_29
  recurrence2A3_coeff_30
  recurrence2A3_coeff_31
  recurrence2A3_coeff_32
  recurrence2A3_coeff_33
  recurrence2A3_coeff_34
  recurrence2A3_coeff_35
  recurrence2A3_coeff_36
  recurrence2A3_coeff_37
  recurrence2A3_coeff_38
  recurrence2A3_coeff_39
  recurrence2A3_coeff_40
  recurrence2A3_coeff_41
  recurrence2A3_coeff_42
  recurrence2A3_coeff_43
  recurrence2A3_coeff_44
  recurrence2A3_coeff_45
  recurrence2A3_coeff_46
  recurrence2A3_coeff_47
  recurrence2A3_coeff_48
  recurrence2A3_coeff_49
  recurrence2A3_coeff_50
  recurrence2A3_coeff_51
  recurrence2A3_coeff_52
  recurrence2A3_coeff_53
  recurrence2A3_coeff_54
  recurrence2A3_coeff_55
  recurrence2A3_coeff_56
  recurrence2A3_coeff_57
  recurrence2A3_coeff_58
  recurrence2A3_coeff_59
  recurrence2A3_coeff_60
  recurrence2A3_coeff_61
  recurrence2A3_coeff_62
  recurrence2A3_coeff_63
  recurrence2A3_coeff_64
  recurrence2A3_coeff_65
  recurrence2A3_coeff_66
  recurrence2A3_coeff_67
  recurrence2A3_coeff_68
  recurrence2A3_coeff_69
  recurrence2A3_coeff_70
  recurrence2A3_coeff_71
  recurrence2A3_coeff_72
  recurrence2A3_coeff_73
  recurrence2A3_coeff_74
  recurrence2A3_coeff_75
  recurrence2A3_coeff_76
  recurrence2A3_coeff_77
  recurrence2A3_coeff_78
  recurrence2A3_coeff_79
  recurrence2A3_coeff_80
  recurrence2A3_coeff_81
  recurrence2A3_coeff_82
  recurrence2A3_coeff_83
  recurrence2A3_coeff_84
  recurrence2A3_coeff_85
  recurrence2A3_coeff_86
  recurrence2A3_coeff_87
  recurrence2A3_coeff_88
  recurrence2A3_coeff_89
  recurrence2A3_coeff_90
  recurrence2A3_coeff_91
  recurrence2A3_coeff_92
  recurrence2A3_coeff_93
  recurrence2A3_coeff_94
  recurrence2A3_coeff_95
  recurrence2A3_coeff_96
  recurrence2A3_coeff_97
  recurrence2A3_coeff_98
  recurrence2A3_coeff_99
  recurrence2A3_coeff_100
  recurrence2A3_coeff_101
  recurrence2A3_coeff_102
  recurrence2A3_coeff_103
  recurrence2A3_coeff_104
  recurrence2A3_coeff_105
  recurrence2A3_coeff_106

theorem recurrence2Scalar3Left_coeff_0 :
    recurrence2Scalar3Left.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_1 :
    recurrence2Scalar3Left.coeff 1 =
      (-245760 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_2 :
    recurrence2Scalar3Left.coeff 2 =
      (687245312 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_3 :
    recurrence2Scalar3Left.coeff 3 =
      (-9256293744576 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_4 :
    recurrence2Scalar3Left.coeff 4 =
      (30125217094481216 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_5 :
    recurrence2Scalar3Left.coeff 5 =
      (-71050586121319762032 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_6 :
    recurrence2Scalar3Left.coeff 6 =
      (311760030220255739426608 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_7 :
    recurrence2Scalar3Left.coeff 7 =
      (338934473124034921396472352 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_8 :
    recurrence2Scalar3Left.coeff 8 =
      (-372161296286781465245466607876 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_9 :
    recurrence2Scalar3Left.coeff 9 =
      (603742422986770487146438708710444 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_10 :
    recurrence2Scalar3Left.coeff 10 =
      (-456718416651077057108147616929121136 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_11 :
    recurrence2Scalar3Left.coeff 11 =
      (278317280540231373999369627371644994768 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_12 :
    recurrence2Scalar3Left.coeff 12 =
      (-131869353245064667288454540673336426817704 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_13 :
    recurrence2Scalar3Left.coeff 13 =
      (45748469501893500238647114360638762580127324 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_14 :
    recurrence2Scalar3Left.coeff 14 =
      (-12128709964311914042867738708995566102663554032 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_15 :
    recurrence2Scalar3Left.coeff 15 =
      (2459054115218102255755713392975425238930980471332 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_16 :
    recurrence2Scalar3Left.coeff 16 =
      (-384729505548982166948654861171654778370809941611896 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_17 :
    recurrence2Scalar3Left.coeff 17 =
      (45535789306667430074554415923027111452112235322760896 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_18 :
    recurrence2Scalar3Left.coeff 18 =
      (-3823547880900833013131431428802165226305817965174888277 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_19 :
    recurrence2Scalar3Left.coeff 19 =
      (175004428538837092561553054708575013731086940907522039817 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_20 :
    recurrence2Scalar3Left.coeff 20 =
      (6398142727807668921588816599497444558986447853128729064391 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_21 :
    recurrence2Scalar3Left.coeff 21 =
      (-2179402807363742550636303749448984651195103924162141914339311 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_22 :
    recurrence2Scalar3Left.coeff 22 =
      (245176608425451463427662055226031868551627850303688629855524249 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_23 :
    recurrence2Scalar3Left.coeff 23 =
      (-18618980063502709257367472575574750179185365310794911661228763717 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_24 :
    recurrence2Scalar3Left.coeff 24 =
      (1068109329996553308050376422599327097821858002281409864901739734401 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_25 :
    recurrence2Scalar3Left.coeff 25 =
      (-47441384615457273023222157503445983843388678138288271285931412995983 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_26 :
    recurrence2Scalar3Left.coeff 26 =
      (1540059667603449985033226832346467097546296323183751632404778480940538 : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_27 :
    recurrence2Scalar3Left.coeff 27 =
      -((2 * 10 ^ 70 +
        2057596737375442048129240974481777422007737454398012343917049093996872) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_28 :
    recurrence2Scalar3Left.coeff 28 =
      -((160 * 10 ^ 70 +
        3711392152711451611967621514692520230788940312813453291491626695096234) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_29 :
    recurrence2Scalar3Left.coeff 29 =
      ((18062 * 10 ^ 70 +
        3731039818426984192014415344363698081178816960635746493360433385202710) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_30 :
    recurrence2Scalar3Left.coeff 30 =
      -((1108058 * 10 ^ 70 +
        5988972274404202657412318490712847769337503169679000206620301804389038) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_31 :
    recurrence2Scalar3Left.coeff 31 =
      ((49967087 * 10 ^ 70 +
        6429679646239649691417753552573760073221414624939560022623878319540667) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_32 :
    recurrence2Scalar3Left.coeff 32 =
      -((1713394123 * 10 ^ 70 +
        5146952897406614493822909311821871416645100990250275332421609428548499) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_33 :
    recurrence2Scalar3Left.coeff 33 =
      ((40643247191 * 10 ^ 70 +
        1240018961738461227092770984053346643315121551234855756511418886872395) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_34 :
    recurrence2Scalar3Left.coeff 34 =
      -((224627461461 * 10 ^ 70 +
        1512112860241754992000107358750264107792239355346452129889032042576039) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_35 :
    recurrence2Scalar3Left.coeff 35 =
      -((42947228664254 * 10 ^ 70 +
        2144334965758465319280485382728463509430058785165192699605777932126774) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_36 :
    recurrence2Scalar3Left.coeff 36 =
      ((3134354329988829 * 10 ^ 70 +
        6901110973877362801495978576344775269745982378768536804247339870037040) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_37 :
    recurrence2Scalar3Left.coeff 37 =
      -((143433832156514698 * 10 ^ 70 +
        1946663384672290065004332484600209949956107870479876892718342180297556) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_38 :
    recurrence2Scalar3Left.coeff 38 =
      ((4933223796638204263 * 10 ^ 70 +
        0620693561004447120307324733506150867153309222749817363997988468556571) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_39 :
    recurrence2Scalar3Left.coeff 39 =
      -((127872946059917261382 * 10 ^ 70 +
        7246838948355878036965947593384827662991091844906069979842657215908883) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_40 :
    recurrence2Scalar3Left.coeff 40 =
      ((2224690320310088765149 * 10 ^ 70 +
        1908235475185135263553371703151235146867759194512661202420116256573490) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_41 :
    recurrence2Scalar3Left.coeff 41 =
      -((9352208636275718022210 * 10 ^ 70 +
        3852834873375798916078767899026660917317784044378707404169693944621950) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_42 :
    recurrence2Scalar3Left.coeff 42 =
      -((1007972341566048561635064 * 10 ^ 70 +
        7639173192316251079778411151600425858933929607984349354870047656602192) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_43 :
    recurrence2Scalar3Left.coeff 43 =
      ((46181671834291773002447720 * 10 ^ 70 +
        1308575198512383143656485117047874379561640923894564721654574822801185) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_44 :
    recurrence2Scalar3Left.coeff 44 =
      -((1319891967077812779628888123 * 10 ^ 70 +
        5419642692182095813163840754006804328111006339158061842492829378441401) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_45 :
    recurrence2Scalar3Left.coeff 45 =
      ((31327451792552796525757672466 * 10 ^ 70 +
        7317408270089723607489678554252491740657781162627882681291405005739359) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_46 :
    recurrence2Scalar3Left.coeff 46 =
      -((727331151093621652333920025390 * 10 ^ 70 +
        7118186533989183940466400006165453694031921241447414215501908385472631) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_47 :
    recurrence2Scalar3Left.coeff 47 =
      ((18181002880584541846740582736254 * 10 ^ 70 +
        2490224216449398454721689836623418151349583827743846416933424814325689) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_48 :
    recurrence2Scalar3Left.coeff 48 =
      -((474079087292926724418473427561272 * 10 ^ 70 +
        5324270139942909390222863137215978335814300238492304164875957935239764) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_49 :
    recurrence2Scalar3Left.coeff 49 =
      ((11771999972251108122944110116274285 * 10 ^ 70 +
        1364871538513053393607895386496201027353341007049697674766784462265150) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_50 :
    recurrence2Scalar3Left.coeff 50 =
      -((261346174293242024937339792115637758 * 10 ^ 70 +
        0873610213342881809835690357355103611183638237936985401881697165872803) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_51 :
    recurrence2Scalar3Left.coeff 51 =
      ((5031940621009312687011833085238619096 * 10 ^ 70 +
        0688014332257412528835598153890335756133498952142521901281610692285648) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_52 :
    recurrence2Scalar3Left.coeff 52 =
      -((82130754007047038771906828616078899611 * 10 ^ 70 +
        4045770201602963205526260720844515910347287723321092679982466569747044) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_53 :
    recurrence2Scalar3Left.coeff 53 =
      ((1084536306817753280772516725387128674919 * 10 ^ 70 +
        7974675663997422203930420474732868669345965971644608838886692866210305) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_54 :
    recurrence2Scalar3Left.coeff 54 =
      -((9784510427231693939826234571964980428028 * 10 ^ 70 +
        1988625765663025393652974930185905522179794586028054845255032120114445) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_55 :
    recurrence2Scalar3Left.coeff 55 =
      -((5750488658510595088669447162954449656815 * 10 ^ 70 +
        6728287061737061329106597142763797009777723569791255116799836383897196) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_56 :
    recurrence2Scalar3Left.coeff 56 =
      ((2840896520662452137193306299260353071398606 * 10 ^ 70 +
        1843427073180680618658001882136045248430163835048304574612362145962969) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_57 :
    recurrence2Scalar3Left.coeff 57 =
      -((83341169731321662290956484358300712974087597 * 10 ^ 70 +
        7199451938771797580444316071555484927993085572826198399047104795814678) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_58 :
    recurrence2Scalar3Left.coeff 58 =
      ((1730920678101355993505253028341155448530562504 * 10 ^ 70 +
        8826763943963402805532810102770334750260121916488323724942598542320309) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_59 :
    recurrence2Scalar3Left.coeff 59 =
      -((29713163917223402917971295612156346030453358162 * 10 ^ 70 +
        9987564993685897299169565927052339118616193697399994081076022408888543) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_60 :
    recurrence2Scalar3Left.coeff 60 =
      ((437899282647239075946203778780440414745355929952 * 10 ^ 70 +
        8385884224149954747881237721523394321849714855933596309501488295569768) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_61 :
    recurrence2Scalar3Left.coeff 61 =
      -((5524595768264981517066942237061700763214474894040 * 10 ^ 70 +
        7321529263379914539918504811059912122893137421470572627999465782093711) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_62 :
    recurrence2Scalar3Left.coeff 62 =
      ((56948185678460688426802494670931488502758626733714 * 10 ^ 70 +
        2736473575698884502192473896394493792288550205790119583746919547044535) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_63 :
    recurrence2Scalar3Left.coeff 63 =
      -((396328172124407472000469707653905375504151391074111 * 10 ^ 70 +
        6832977091098696697153484989179652868945371775478230608822637467010398) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_64 :
    recurrence2Scalar3Left.coeff 64 =
      -((621005887149142592384921192149849874840117697030578 * 10 ^ 70 +
        7739801773687424940342775071571933927691966931036293247858835258988140) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_65 :
    recurrence2Scalar3Left.coeff 65 =
      ((87618736010987108224239543104735877209679448869551142 * 10 ^ 70 +
        5523288531519408030285282148876975809945351940125543939410655553300244) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_66 :
    recurrence2Scalar3Left.coeff 66 =
      -((2063964997857926450398075459130548922795296660299383373 * 10 ^ 70 +
        5436024345048438845810230668568177801588688151990467100950982164201764) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_67 :
    recurrence2Scalar3Left.coeff 67 =
      ((35724248171161328208723973124713435850124627050507765471 * 10 ^ 70 +
        2456265592158240131554351920458175247111446742171043626447308870553275) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_68 :
    recurrence2Scalar3Left.coeff 68 =
      -((527513824611510836694545306721378392464672888277741562973 * 10 ^ 70 +
        1371831601672213236579825699579972351118872472701800884387642235027754) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_69 :
    recurrence2Scalar3Left.coeff 69 =
      ((6988946149027836292586165725820362333223229848387302527532 * 10 ^ 70 +
        1842896040150225946724181525655129091163273296121915830448226885925849) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_70 :
    recurrence2Scalar3Left.coeff 70 =
      -((85068447728416971702300173025293943348208641284131361050676 * 10 ^ 70 +
        9518547940925781539305732348755735332649780018903062874698506739780326) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_71 :
    recurrence2Scalar3Left.coeff 71 =
      ((963911507191639691212903573642204379156169344598023090154249 * 10 ^ 70 +
        0555084167036874844117715084339860882113685736726844263490362484897370) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_72 :
    recurrence2Scalar3Left.coeff 72 =
      -((10251729313403730120276074479586266180544349277136053132530266 * 10 ^ 70 +
        8370327500278002440237446046111880114218407655259700068324793480775324) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_73 :
    recurrence2Scalar3Left.coeff 73 =
      ((102914566201746902042910215021696123643863814457592057490310718 * 10 ^ 70 +
        8846088629137240213864782209109544100687648947157517305398252368797967) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_74 :
    recurrence2Scalar3Left.coeff 74 =
      -((979120365354053779779598280675636051490815534805224248713448863 * 10 ^ 70 +
        3126285335852912867542297211354582640099117875502443521687438700966095) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_75 :
    recurrence2Scalar3Left.coeff 75 =
      ((8855571467083609885755367581398847405733906933704680612784342214 * 10 ^ 70 +
        9148584252590661799271527147934166224705011831432576261316909919290984) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_76 :
    recurrence2Scalar3Left.coeff 76 =
      -((76326886423588361372130689156088414643630979451880821455761122661 * 10 ^ 70 +
        6582584721239302844985022382362543107000223681713863065589236372139299) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_77 :
    recurrence2Scalar3Left.coeff 77 =
      ((628161244608972405569101414228266327812221205348278473454421004593 * 10 ^ 70 +
        4839170749728233649152169721903198817603763426843607447818595280182319) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_78 :
    recurrence2Scalar3Left.coeff 78 =
      -((4944108750732081274829737173855612925551257658177368175943149411637 * 10 ^ 70 +
        9191014050254834806711690423637629208072503510493473006518223111629665) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_79 :
    recurrence2Scalar3Left.coeff 79 =
      ((37263953870491220747868528518260401825231120786702889540285187286938 * 10 ^ 70 +
        0898517954918517094103058096183146652383489411247236054733506151741571) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_80 :
    recurrence2Scalar3Left.coeff 80 =
      -((269234482113354249417593310833989763124708593287623895226829574730091 * 10 ^ 70 +
        2468948449543457472416356659068603260681018450106240137886724080260559) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_81 :
    recurrence2Scalar3Left.coeff 81 =
      ((1866331191926036038808599987960202519031561977543592090014984403632639 * 10 ^ 70 +
        9122327021325348313104516310231098367373110941739577532431847336739241) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_82 :
    recurrence2Scalar3Left.coeff 82 =
      -(((1 * 10 ^ 70 +
        2421543676983478364626835218362415449320410882856962403037827901279277) * 10 ^ 70 +
        8037010575574319492337772758721520833698986611436946564864600701001820) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_83 :
    recurrence2Scalar3Left.coeff 83 =
      (((7 * 10 ^ 70 +
        9424186561875074830797285803764259835306991264639476259990641103494073) * 10 ^ 70 +
        2886763208486711646316462826158718565712148726337630471733138702403987) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_84 :
    recurrence2Scalar3Left.coeff 84 =
      -(((48 * 10 ^ 70 +
        8128876780736136679619153810497174994769517701346413834517600756675673) * 10 ^ 70 +
        9648133810543434615408011092894350232956027340221519649565836865644963) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_85 :
    recurrence2Scalar3Left.coeff 85 =
      (((288 * 10 ^ 70 +
        4583555775376393159428873936933558507374491089298079907531032274674260) * 10 ^ 70 +
        6219327554703322469927993193537759779214867573748207710525019750504551) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_86 :
    recurrence2Scalar3Left.coeff 86 =
      -(((1639 * 10 ^ 70 +
        4541863226844702405186963501503114766531727573534323315429060310470245) * 10 ^ 70 +
        9505602863807752581411736845558392626694747671781154296268778199034485) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_87 :
    recurrence2Scalar3Left.coeff 87 =
      (((8962 * 10 ^ 70 +
        1230735438752633436863020284877156335428964841711466963212634963531006) * 10 ^ 70 +
        4715203882529490512315181435259765585334565405605550886471883418653349) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_88 :
    recurrence2Scalar3Left.coeff 88 =
      -(((47115 * 10 ^ 70 +
        7069318047299819360231910968385873018094013189547479024148068319717008) * 10 ^ 70 +
        1401788653534415995740575915093694042714822102318863269048470442338926) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_89 :
    recurrence2Scalar3Left.coeff 89 =
      (((238138 * 10 ^ 70 +
        3576497312540170336968610577202958655422709036794390217529272780917643) * 10 ^ 70 +
        8480677985342958135306687964312451993295977826403268803281369406890338) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_90 :
    recurrence2Scalar3Left.coeff 90 =
      -(((1156607 * 10 ^ 70 +
        3348835319110668265951497574604253866696968400045048104916348773239066) * 10 ^ 70 +
        6742403946821895053550605871368062147579640971589466492210519932330306) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_91 :
    recurrence2Scalar3Left.coeff 91 =
      (((5394253 * 10 ^ 70 +
        1684234993015372976951940990338806509992266196763260292259750194227023) * 10 ^ 70 +
        3220000916755377329271418582561661212119067751959561322043155202562814) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_92 :
    recurrence2Scalar3Left.coeff 92 =
      -(((24134776 * 10 ^ 70 +
        6430055112302294871553258127315624339222251367162639466430990326121522) * 10 ^ 70 +
        3773623959900046007268680068994182600924517601496585375560632327868620) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_93 :
    recurrence2Scalar3Left.coeff 93 =
      (((103445039 * 10 ^ 70 +
        9414222321412703311885806515729194012711316920504910203133858532695494) * 10 ^ 70 +
        7169503964653601580013335507906845274711364324025787240057062328650545) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_94 :
    recurrence2Scalar3Left.coeff 94 =
      -(((423834527 * 10 ^ 70 +
        8762674379319237814003362758503676647629663154179335027339510601578734) * 10 ^ 70 +
        0142096967191625838214544676074216948753852618553545766224663646152991) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_95 :
    recurrence2Scalar3Left.coeff 95 =
      (((1654391493 * 10 ^ 70 +
        7142469275285816920461366372838889333615640076635505929719670698312530) * 10 ^ 70 +
        8132268920317409342311819272813190370400968400053902749675594859793422) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_96 :
    recurrence2Scalar3Left.coeff 96 =
      -(((6119657526 * 10 ^ 70 +
        4217308184937457456420597163524812760250518286031732490107183791680495) * 10 ^ 70 +
        3099879679754975689057561641816408042345551564876562139681391000939818) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_97 :
    recurrence2Scalar3Left.coeff 97 =
      (((21272068851 * 10 ^ 70 +
        5740048437286112275029980064612081843733578111624596479245504379560644) * 10 ^ 70 +
        8943683785538748247078030591828253544796060421940367463706268694515765) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_98 :
    recurrence2Scalar3Left.coeff 98 =
      -(((68535001491 * 10 ^ 70 +
        2981272089149711215228715101687712419769227230926755683414649098989151) * 10 ^ 70 +
        4533832157933755072387675268879735080191556083054601706026111122966219) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_99 :
    recurrence2Scalar3Left.coeff 99 =
      (((199670315917 * 10 ^ 70 +
        2461553692976839594767685830140891926958257422104684692794083608285817) * 10 ^ 70 +
        3639631970244661021043267173373982715211711825173333089744958540710817) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_100 :
    recurrence2Scalar3Left.coeff 100 =
      -(((498552737113 * 10 ^ 70 +
        5832587354032183667508095836991954913110209681249657222967910229345629) * 10 ^ 70 +
        0065185795333723063118208808978848509682087272222312295050922027298526) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_101 :
    recurrence2Scalar3Left.coeff 101 =
      (((899767219523 * 10 ^ 70 +
        7094826279647773271587314714325680759663947069473529658172087786169497) * 10 ^ 70 +
        3505579220408860277668388377536796280340195598942975994083080429054398) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_102 :
    recurrence2Scalar3Left.coeff 102 =
      (((22698422959 * 10 ^ 70 +
        9887843670533982096001699750252130464446449091810321358316688039066891) * 10 ^ 70 +
        3579578480785650054424250578018435858005839445439017492936523497875245) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_103 :
    recurrence2Scalar3Left.coeff 103 =
      -(((10946793268439 * 10 ^ 70 +
        6025701607538525713458967940651394155639728540792595275503003055686207) * 10 ^ 70 +
        9748877430402428701360338214947973984332745310688373657729355442393017) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_104 :
    recurrence2Scalar3Left.coeff 104 =
      (((72837771131421 * 10 ^ 70 +
        8603264421681294536095090947517662429476587758980132729456820922731390) * 10 ^ 70 +
        7285961491124432546140559590750944323180519607566451664794433681884691) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_105 :
    recurrence2Scalar3Left.coeff 105 =
      -(((356123258335447 * 10 ^ 70 +
        2092153023301527345390682509193901503044877638245571871490027948287306) * 10 ^ 70 +
        1527961587207633870124957708345525964237448588877077531941747141647116) : ℚ) := by
  unfold recurrence2Scalar3Left
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

theorem recurrence2Scalar3Left_coeff_106 :
    recurrence2Scalar3Left.coeff 106 =
      (((1502139469061387 * 10 ^ 70 +
        8220500302518783677367468372693413346373875425729750772536906500513389) * 10 ^ 70 +
        8581055999567338884922503712045872494010161972257008961403728898192390) : ℚ) := by
  unfold recurrence2Scalar3Left
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

private theorem recurrence2Scalar3Left_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_107 :
    recurrence2Scalar3Left.coeff 107 =
      -(((5651282527999003 * 10 ^ 70 +
        4024931914036031349576583961408141461332216040913929362006804122983039) * 10 ^ 70 +
        7142143893563977618143927862718972224469867817365669222679744451787271) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 108 = 1 +
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
  rw [recurrence2Scalar3Left_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_108 :
    recurrence2Scalar3Left.coeff 108 =
      (((18740813677517454 * 10 ^ 70 +
        1377642533094159064052691646619213913357827544983910822312395802094199) * 10 ^ 70 +
        6197449892582378453523527401584425024300354321009067690254618699757501) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 109 = 2 +
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
  rw [recurrence2Scalar3Left_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_109 :
    recurrence2Scalar3Left.coeff 109 =
      -(((52295590832440833 * 10 ^ 70 +
        3263555581108984414562500508881283547072070074901902026533367711541889) * 10 ^ 70 +
        4603120483167404311589936419463587478561831820465715932503524037375698) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 110 = 3 +
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
  rw [recurrence2Scalar3Left_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_110 :
    recurrence2Scalar3Left.coeff 110 =
      (((110836826115150712 * 10 ^ 70 +
        9932741146629241291271839175280440389913150190444756015217850741362462) * 10 ^ 70 +
        9516710507726686652725082170320590607551371349410545173536228175968998) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 111 = 4 +
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
  rw [recurrence2Scalar3Left_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_111 :
    recurrence2Scalar3Left.coeff 111 =
      -(((134679665303745869 * 10 ^ 70 +
        3342072013126133843757017125035342544752728235078436116433061284510532) * 10 ^ 70 +
        3055192195846499012672685324814626391832980672538680642123113905417060) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 5 +
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
  rw [recurrence2Scalar3Left_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_112 :
    recurrence2Scalar3Left.coeff 112 =
      (((14307171402344140 * 10 ^ 70 +
        0648499688132798678997508401298964923009864557824328685793256399024811) * 10 ^ 70 +
        2682106522661295825374850540296291701232830210246001099536353453198954) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 6 +
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
  rw [recurrence2Scalar3Left_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_113 :
    recurrence2Scalar3Left.coeff 113 =
      -(((909868940932449058 * 10 ^ 70 +
        8451089841313412450146931331596205145248419169590355160478455688919765) * 10 ^ 70 +
        7836787837287054811891455037878808661897135277346137020451583944268453) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 7 +
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
  rw [recurrence2Scalar3Left_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_114 :
    recurrence2Scalar3Left.coeff 114 =
      (((12545028945744913716 * 10 ^ 70 +
        9023351436244669548367077038752378598749112754337083740466116776670890) * 10 ^ 70 +
        7079265002513749384047572451606632758278487829972029363293939039515781) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 8 +
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
  rw [recurrence2Scalar3Left_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_115 :
    recurrence2Scalar3Left.coeff 115 =
      -(((69931331004428214736 * 10 ^ 70 +
        1025631144851655626674592961116613326377408219088573766293440122755691) * 10 ^ 70 +
        9851104294497015543551037306220764004435554901866626620434029858748289) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 9 +
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
  rw [recurrence2Scalar3Left_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_116 :
    recurrence2Scalar3Left.coeff 116 =
      (((195614029625201547601 * 10 ^ 70 +
        3907183933298549409458370100338554125393625546548888510254628320587886) * 10 ^ 70 +
        3837905155957013355483808146388483109486736138224714332666683954647012) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 10 +
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
  rw [recurrence2Scalar3Left_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_117 :
    recurrence2Scalar3Left.coeff 117 =
      (((122104133259660316640 * 10 ^ 70 +
        1888726775874264848550783308980582288802267485508227025039458092324844) * 10 ^ 70 +
        9035451463329768810824612673397077575721174582859568478165508285813174) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 11 +
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
  rw [recurrence2Scalar3Left_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_118 :
    recurrence2Scalar3Left.coeff 118 =
      -(((4410648128333652379929 * 10 ^ 70 +
        8495835626041189267582049718079465747636823003068139227310090246796758) * 10 ^ 70 +
        4439456370539288600260662068231696085188776195522046261395311252207817) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 12 +
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
  rw [recurrence2Scalar3Left_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_119 :
    recurrence2Scalar3Left.coeff 119 =
      (((25732869909476928997163 * 10 ^ 70 +
        6232673571394871810973249419294374787575153472160827826543095402979246) * 10 ^ 70 +
        3557937423329102199380481627768821375105009096189154295050694993562730) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 13 +
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
  rw [recurrence2Scalar3Left_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_120 :
    recurrence2Scalar3Left.coeff 120 =
      -(((87995171537844488252111 * 10 ^ 70 +
        4058592010607365208628506099966103646224423897039118899777334798642085) * 10 ^ 70 +
        3227934488972829854107187512422735458457199120703494155441682097189766) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 14 +
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
  rw [recurrence2Scalar3Left_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_121 :
    recurrence2Scalar3Left.coeff 121 =
      (((141226171379609334527202 * 10 ^ 70 +
        5577321576005201831963132142478314155861645214338689343044351686899981) * 10 ^ 70 +
        6715746134013386059417265317057323161816086630292296425736798634454699) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 15 +
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
  rw [recurrence2Scalar3Left_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_122 :
    recurrence2Scalar3Left.coeff 122 =
      (((423771464821791902368416 * 10 ^ 70 +
        5052095359097365101867579863265895072415033375179896911201134454274034) * 10 ^ 70 +
        9744710305365372392274051293335210318319541436842168758835385111595458) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 16 +
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
  rw [recurrence2Scalar3Left_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_123 :
    recurrence2Scalar3Left.coeff 123 =
      -(((4236295619253702246046679 * 10 ^ 70 +
        5862391625740698583590323021470523098369116707004090247566275155349723) * 10 ^ 70 +
        8741770757875389994286465611075145287587814621968483759584972821029863) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 17 +
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
  rw [recurrence2Scalar3Left_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_124 :
    recurrence2Scalar3Left.coeff 124 =
      (((17376999162379349371105479 * 10 ^ 70 +
        0193038929191122890834288548630337131563037616226398371283554599684775) * 10 ^ 70 +
        9884429025886483336997943551124953975660913444414231523147288742604288) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 18 +
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
  rw [recurrence2Scalar3Left_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_125 :
    recurrence2Scalar3Left.coeff 125 =
      -(((41001012652426581435073881 * 10 ^ 70 +
        5640845341053863372225760439232457735562486648010318993398818123406971) * 10 ^ 70 +
        9612503016206713236504092494899245078852616876506143655629593799154801) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 19 +
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
  rw [recurrence2Scalar3Left_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_126 :
    recurrence2Scalar3Left.coeff 126 =
      (((30022033036802336201918195 * 10 ^ 70 +
        1145878447010762552052090134517985093515714250128922426431282792367855) * 10 ^ 70 +
        3029317598499325486067391210476923831368932610576232785726991528270535) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 20 +
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
  rw [recurrence2Scalar3Left_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_127 :
    recurrence2Scalar3Left.coeff 127 =
      (((189485725763189480830896124 * 10 ^ 70 +
        5636614347944240752219454418178476774731515720303130702613884391625171) * 10 ^ 70 +
        7931590193327647387629712165532079187912024481446527339562758609703106) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 21 +
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
  rw [recurrence2Scalar3Left_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_128 :
    recurrence2Scalar3Left.coeff 128 =
      -(((1282743606075811208361215626 * 10 ^ 70 +
        4442818312208865946968953633846503597114387165360622565905812909411502) * 10 ^ 70 +
        6583988808742687810905514106696507240985715578347855416106526820202008) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 22 +
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
  rw [recurrence2Scalar3Left_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_129 :
    recurrence2Scalar3Left.coeff 129 =
      (((8352124395535514568726062114 * 10 ^ 70 +
        1137262840688423261685626498873031021602695380561373564613378088956750) * 10 ^ 70 +
        7360026381288396258640239404175457210563984156403347147752600654814466) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 23 +
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
  rw [recurrence2Scalar3Left_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_130 :
    recurrence2Scalar3Left.coeff 130 =
      -(((52601346865285851541074793708 * 10 ^ 70 +
        3430228387455613562188773338870665958724382817713355967857266935814215) * 10 ^ 70 +
        2739920082457676513308333023470690741693415240143803221516784444877016) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 24 +
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
  rw [recurrence2Scalar3Left_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_131 :
    recurrence2Scalar3Left.coeff 131 =
      (((222430186860787891856295567847 * 10 ^ 70 +
        9217397632893676399522651215184764258079655903620210878765938599688396) * 10 ^ 70 +
        0755627384436633695166710853740541913132092400083736810209324999387764) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 25 +
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
  rw [recurrence2Scalar3Left_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_132 :
    recurrence2Scalar3Left.coeff 132 =
      -(((328163762320932045499596825262 * 10 ^ 70 +
        6460127423919093119517683427669672318033878589149506689119726139235581) * 10 ^ 70 +
        1889349256026632209652257777747396385767463560303204357902096819905821) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 26 +
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
  rw [recurrence2Scalar3Left_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_133 :
    recurrence2Scalar3Left.coeff 133 =
      -(((2546216153629515030299285707805 * 10 ^ 70 +
        5038597818956199214863743758163386574391663063738054296929854166700150) * 10 ^ 70 +
        2845554467582852614441720155627118731099747702684161683117808546255760) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 27 +
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
  rw [recurrence2Scalar3Left_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_134 :
    recurrence2Scalar3Left.coeff 134 =
      (((20108709110024352826408681355503 * 10 ^ 70 +
        0630685760772016400856469961119871226230150726622021392938534233524817) * 10 ^ 70 +
        2914175096511526694616905718727130040071298075597487491575604418666774) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 28 +
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
  rw [recurrence2Scalar3Left_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_135 :
    recurrence2Scalar3Left.coeff 135 =
      -(((60586279358066777323656322118290 * 10 ^ 70 +
        6929430986192529041269703077173208282873228200708385977828135067295567) * 10 ^ 70 +
        2744516785693142036213538772727187198360998515687367131459079264997123) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 29 +
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
  rw [recurrence2Scalar3Left_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_136 :
    recurrence2Scalar3Left.coeff 136 =
      -(((14631597899471884459744259347653 * 10 ^ 70 +
        4109434631696198518091072907297211179986899456011298596471124441446171) * 10 ^ 70 +
        8212738901209114339814367990969187459365612044262925768131162301424074) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 30 +
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
  rw [recurrence2Scalar3Left_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_137 :
    recurrence2Scalar3Left.coeff 137 =
      (((879824119154502345971705902722325 * 10 ^ 70 +
        7278875545389320613409191332558005557277384784170944848203826441167596) * 10 ^ 70 +
        7698254843331773940285160933124496872287787884188852428558409099661636) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 31 +
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
  rw [recurrence2Scalar3Left_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_138 :
    recurrence2Scalar3Left.coeff 138 =
      -(((3204195787631218458019929785599990 * 10 ^ 70 +
        2009329586598033438176396148360588956520898952230691515273345428391863) * 10 ^ 70 +
        0318629687203679053436979088013187182021615727117652339589848466494703) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 32 +
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
  rw [recurrence2Scalar3Left_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_139 :
    recurrence2Scalar3Left.coeff 139 =
      (((426249082344839371485511614100217 * 10 ^ 70 +
        3613158835267455853460663612124912550120975624729900683492981262319433) * 10 ^ 70 +
        6951135357759605278712456924890296401779749526081859607218976190463820) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 33 +
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
  rw [recurrence2Scalar3Left_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_140 :
    recurrence2Scalar3Left.coeff 140 =
      (((38950773347197931221636323656561311 * 10 ^ 70 +
        3838959829672086031550490955818454826738434752683607344594882973414025) * 10 ^ 70 +
        9463435213129729617701110492797890160460181016782506705460541178615073) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 34 +
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
  rw [recurrence2Scalar3Left_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_141 :
    recurrence2Scalar3Left.coeff 141 =
      -(((134420371029992410586884160182418701 * 10 ^ 70 +
        6306214000571616621468897777214892723535160503524102637846881934687616) * 10 ^ 70 +
        9230696117212061843123367791890550372395014263499575845122219629747955) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 35 +
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
  rw [recurrence2Scalar3Left_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_142 :
    recurrence2Scalar3Left.coeff 142 =
      -(((67324042751100110322608191953903741 * 10 ^ 70 +
        4566121092757963377386196700007874815969759079671415237488016804092537) * 10 ^ 70 +
        4563784233669444666981987043508279883777446400579710271264851403488191) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 36 +
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
  rw [recurrence2Scalar3Left_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_143 :
    recurrence2Scalar3Left.coeff 143 =
      (((2009024418202604696162928084955915129 * 10 ^ 70 +
        5692285771269903349816698488693847648615734599869915142672399452464392) * 10 ^ 70 +
        4573226701133528694372947386560554228311921269453406698937634466777637) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 37 +
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
  rw [recurrence2Scalar3Left_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_144 :
    recurrence2Scalar3Left.coeff 144 =
      -(((5900019878993257546007213070669656214 * 10 ^ 70 +
        1786179150995706897837643539078349258685835356279848574931180721336776) * 10 ^ 70 +
        5904159342302229329334411454875608150556622076878366255553638610226750) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 38 +
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
  rw [recurrence2Scalar3Left_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_145 :
    recurrence2Scalar3Left.coeff 145 =
      -(((5942728167108887040019758744039403471 * 10 ^ 70 +
        9380496376672800167560529182362937516812962911232268346783686857625543) * 10 ^ 70 +
        0260809829995413782593176338935278631654504881627529149051245613723471) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 39 +
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
  rw [recurrence2Scalar3Left_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_146 :
    recurrence2Scalar3Left.coeff 146 =
      (((92324814218846992341167338889323271564 * 10 ^ 70 +
        2666396547019309426320395130599828142869164427582466836036192331404130) * 10 ^ 70 +
        3406683581704047665285543354289238533767285309518727668374496196810170) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 40 +
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
  rw [recurrence2Scalar3Left_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_147 :
    recurrence2Scalar3Left.coeff 147 =
      -(((213052435032793665097015250341928409471 * 10 ^ 70 +
        8574547249638490657659357900624458875449686248230598283650019210759403) * 10 ^ 70 +
        7825560123736881559662945553297298980206993690074745440925341300915715) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 41 +
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
  rw [recurrence2Scalar3Left_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_148 :
    recurrence2Scalar3Left.coeff 148 =
      -(((512900683669948921759666543932801395096 * 10 ^ 70 +
        3932454622149861975430960650489897809688371760553198391455995902001202) * 10 ^ 70 +
        7864662112005768429855381424875458771224768246916274820322068137575063) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 42 +
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
  rw [recurrence2Scalar3Left_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_149 :
    recurrence2Scalar3Left.coeff 149 =
      (((4335670100927251382601282677530736186974 * 10 ^ 70 +
        5746878030646038414598625806658563270776263553417884602277309751040982) * 10 ^ 70 +
        5021039477375597659729887787272521817260023629289150426682916318380746) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 43 +
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
  rw [recurrence2Scalar3Left_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_150 :
    recurrence2Scalar3Left.coeff 150 =
      -(((6703398764974515088659339001425166658397 * 10 ^ 70 +
        9611573509427575091864634834112979535648732072835885264686719912043843) * 10 ^ 70 +
        7409194788726790598985854061106960396145329493716586467693405522195713) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 151 = 44 +
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
  rw [recurrence2Scalar3Left_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_151 :
    recurrence2Scalar3Left.coeff 151 =
      -(((38614815188984721040919862625304037713964 * 10 ^ 70 +
        6426335891033077977036597051940144172717851732721966498196872790368613) * 10 ^ 70 +
        6058472475815940915363198630413369303297384009591106923035204992279533) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 152 = 45 +
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
  rw [recurrence2Scalar3Left_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_152 :
    recurrence2Scalar3Left.coeff 152 =
      (((232246658752287030585021998023706676230489 * 10 ^ 70 +
        5963939894197252452444532855167587308942266178100013302528195978681376) * 10 ^ 70 +
        6499728839871943722247973622652231326458957641394345801002294915603522) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 153 = 46 +
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
  rw [recurrence2Scalar3Left_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_153 :
    recurrence2Scalar3Left.coeff 153 =
      -(((313078704343761405774143064014991123697946 * 10 ^ 70 +
        4141954367051828652713320651027594030382925898167512241859388007409424) * 10 ^ 70 +
        5445404887442518750392955612778771660946678735435457622828144540020335) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 47 +
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
  rw [recurrence2Scalar3Left_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_154 :
    recurrence2Scalar3Left.coeff 154 =
      -(((2028823038558636617910099449922526865946444 * 10 ^ 70 +
        0471581576570683320253338620369259536155099864668500397205908785842736) * 10 ^ 70 +
        5999615306676906442406882241765754015444300570153911854063813969473534) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 48 +
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
  rw [recurrence2Scalar3Left_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_155 :
    recurrence2Scalar3Left.coeff 155 =
      (((12106235507761723709481412718113763828591195 * 10 ^ 70 +
        0011889704690463255475253423282784300832031151559147763297191354465166) * 10 ^ 70 +
        2357274714810835339239087912272928382592705623523243367775368497016640) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 49 +
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
  rw [recurrence2Scalar3Left_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_156 :
    recurrence2Scalar3Left.coeff 156 =
      -(((20866046941090793907221752032045870165528658 * 10 ^ 70 +
        3878545408383245514540754021247089608343465011190718899944041994883525) * 10 ^ 70 +
        0149034069479937990020606553859807817462196886590934901473512798951776) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 50 +
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
  rw [recurrence2Scalar3Left_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_157 :
    recurrence2Scalar3Left.coeff 157 =
      -(((71668986560716364131170007278728546214943167 * 10 ^ 70 +
        3581778991077425310849725689837687894508914241087461036020941488239820) * 10 ^ 70 +
        3064186094769332834660678167904887115725794782139414175859203809793838) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 51 +
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
  rw [recurrence2Scalar3Left_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_158 :
    recurrence2Scalar3Left.coeff 158 =
      (((538885170224139691660203758206410118834423024 * 10 ^ 70 +
        6473410125457283064784134242536370229605939417499448433455105008744541) * 10 ^ 70 +
        4715489276701468128122558993748211789319617400890059032705229862434327) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 52 +
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
  rw [recurrence2Scalar3Left_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_159 :
    recurrence2Scalar3Left.coeff 159 =
      -(((1258596178147366633365190643395849495701665330 * 10 ^ 70 +
        9124327731063065275561208891033734461880029699580882577648569858443380) * 10 ^ 70 +
        0118585987509681677480202573900849127298300400368320451539153996274217) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 53 +
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
  rw [recurrence2Scalar3Left_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_160 :
    recurrence2Scalar3Left.coeff 160 =
      -(((1333828244055002734480867511641900060062974945 * 10 ^ 70 +
        4427745176118211423028046177231335603073785975249162541420594923182645) * 10 ^ 70 +
        1610075950279469387283549116958468480630917190462143972744436359600744) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 54 +
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
  rw [recurrence2Scalar3Left_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_161 :
    recurrence2Scalar3Left.coeff 161 =
      (((19382246042479875811501288484560887381053165673 * 10 ^ 70 +
        5389679307415429370108905848600704002316623453131973486824455868067728) * 10 ^ 70 +
        3010243829746091531731102870900934744060914117641920900405787472569023) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 55 +
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
  rw [recurrence2Scalar3Left_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_162 :
    recurrence2Scalar3Left.coeff 162 =
      -(((60198534800153602222200663055464206896545341677 * 10 ^ 70 +
        2245870253559466997600407363844251529838986601568411625865066166005441) * 10 ^ 70 +
        9205572509414563074220015647217309847056523610350796151129118090244238) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 56 +
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
  rw [recurrence2Scalar3Left_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_163 :
    recurrence2Scalar3Left.coeff 163 =
      (((23156488026304377162319007767601186307480966010 * 10 ^ 70 +
        0428983233740373196260696333917678494674220842666747676434569817151990) * 10 ^ 70 +
        0852559955743498661357086340406244263412477087783875497522990638108571) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 57 +
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
  rw [recurrence2Scalar3Left_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_164 :
    recurrence2Scalar3Left.coeff 164 =
      (((543164316382102489288461160232169317785313355431 * 10 ^ 70 +
        0434524609675774341467948858811861055553237704256131375317393011583847) * 10 ^ 70 +
        3034539686803176376086153929737508509833357991367263313454086453560727) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 58 +
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
  rw [recurrence2Scalar3Left_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_165 :
    recurrence2Scalar3Left.coeff 165 =
      -(((2300363545209386506483905856818668796767698300679 * 10 ^ 70 +
        2477369313096952000374802328601976420095631330515152897933592870266449) * 10 ^ 70 +
        6529037909490741793499730640122469507942140247420758775486812251411786) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 59 +
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
  rw [recurrence2Scalar3Left_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_166 :
    recurrence2Scalar3Left.coeff 166 =
      (((3215201748917490317809399554335160471799694073953 * 10 ^ 70 +
        7295249982150557130581722728308776729581801433266011097365666771887942) * 10 ^ 70 +
        6785262193276739883729593945299821127183301060107450969469702205651676) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 60 +
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
  rw [recurrence2Scalar3Left_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_167 :
    recurrence2Scalar3Left.coeff 167 =
      (((10722217551525109399169578751064069752503511310348 * 10 ^ 70 +
        3074432273003270652635532063368856648971190218890311794131385737100867) * 10 ^ 70 +
        3649835759284670426093052718504184335515282085639387735011547051256919) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 61 +
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
  rw [recurrence2Scalar3Left_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_168 :
    recurrence2Scalar3Left.coeff 168 =
      -(((71846410819585812568221198840679619918799373590284 * 10 ^ 70 +
        0607377766105453667753495726233303025147000374559602758175301210462821) * 10 ^ 70 +
        8468236256339107173871223593355028598748132706328307260908381933591898) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 62 +
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
  rw [recurrence2Scalar3Left_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_169 :
    recurrence2Scalar3Left.coeff 169 =
      (((167111267733090785222041643166789205374385906200812 * 10 ^ 70 +
        1296287058335634080112808095712038208726488596097410873206503017396928) * 10 ^ 70 +
        3521465480028670015636236769859124997935057157329758781174988572483987) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 63 +
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
  rw [recurrence2Scalar3Left_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_170 :
    recurrence2Scalar3Left.coeff 170 =
      (((54324962932303328043713297802290909625056072429042 * 10 ^ 70 +
        8471269138181053193386577457051327398458608559090792825583719147128096) * 10 ^ 70 +
        9141137014816205666949154155783475288598772830920165613661453761813313) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 64 +
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
  rw [recurrence2Scalar3Left_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_171 :
    recurrence2Scalar3Left.coeff 171 =
      -(((1777812816944616077195247881145751537144587473629348 * 10 ^ 70 +
        9347631912581663935012743260155624704816088626700976452593047598827377) * 10 ^ 70 +
        0844409281043985850306936601906624016503377162033714924743670285028554) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 65 +
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
  rw [recurrence2Scalar3Left_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_172 :
    recurrence2Scalar3Left.coeff 172 =
      (((6239633556678417314762311336780821712331564593194380 * 10 ^ 70 +
        6703014281669258085307296207051305589182965091691221057745761213300833) * 10 ^ 70 +
        2644404934394238265130630448629215000572213648552075641489790273314745) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 66 +
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
  rw [recurrence2Scalar3Left_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_173 :
    recurrence2Scalar3Left.coeff 173 =
      -(((7465441920806590457458492046793823840335006043896967 * 10 ^ 70 +
        2475711373527639267905827910909543536786430250675131017787217055499315) * 10 ^ 70 +
        7117484287961718743645945445865169071261538726319554674867978068673151) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 67 +
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
  rw [recurrence2Scalar3Left_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_174 :
    recurrence2Scalar3Left.coeff 174 =
      -(((27822449330021422610130733872159812559130294235865333 * 10 ^ 70 +
        2948843007361827546876515061518193904009312371441587403790599945542445) * 10 ^ 70 +
        3780320937541196408081142886217448901294437142976903696988307415972248) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 68 +
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
  rw [recurrence2Scalar3Left_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_175 :
    recurrence2Scalar3Left.coeff 175 =
      (((172978659433033501906963671255301289086401018525689799 * 10 ^ 70 +
        2688466793539896221639483947257870264829741235106652003172236837072305) * 10 ^ 70 +
        1317860974548593635086656420459046985931760058456401040282583191618477) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 69 +
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
  rw [recurrence2Scalar3Left_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_176 :
    recurrence2Scalar3Left.coeff 176 =
      -(((421174721687331079078152859988593118944966495470124373 * 10 ^ 70 +
        8192230847871375813966818349869248829606904648206967248175250286042708) * 10 ^ 70 +
        4257914498968441408444020272231054675230720809260169534273579971067915) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 70 +
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
  rw [recurrence2Scalar3Left_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_177 :
    recurrence2Scalar3Left.coeff 177 =
      (((133978207489105288293880145879786611587102414579488309 * 10 ^ 70 +
        9483783504605251225565180309059856385679288240103505198593464780678782) * 10 ^ 70 +
        6605518807014757822098188441803071543882226527192350860548651264522746) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 71 +
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
  rw [recurrence2Scalar3Left_coeff_177_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_178 :
    recurrence2Scalar3Left.coeff 178 =
      (((3041578743686462163066897774962673481477464902011388653 * 10 ^ 70 +
        9894783776912387972994515948067112097059551680649799110488311032199429) * 10 ^ 70 +
        6706865411549051923422964842694352707039241873923208250651027044612472) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 72 +
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
  rw [recurrence2Scalar3Left_coeff_178_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_179 :
    recurrence2Scalar3Left.coeff 179 =
      -(((12849130351341234646451094824018673369652886728459054864 * 10 ^ 70 +
        7415292521108959833272508507436922533122728322085602970928814193391462) * 10 ^ 70 +
        2668902427541302103563393967100778154226309917023691932458911753126117) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 73 +
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
  rw [recurrence2Scalar3Left_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_180 :
    recurrence2Scalar3Left.coeff 180 =
      (((24831071690516085398876027266646744244273313875398660002 * 10 ^ 70 +
        4489847797206258077090219504904045097647216924870669743015964230048608) * 10 ^ 70 +
        0359197473067833951318448295951135877873279901635500398738336751698340) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 74 +
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
  rw [recurrence2Scalar3Left_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_181 :
    recurrence2Scalar3Left.coeff 181 =
      (((6906150232257897113311297784961912509013108728764321626 * 10 ^ 70 +
        7621713275982994713281325651808808977764856850445388897424284188328108) * 10 ^ 70 +
        1643349675044743416362973756005300809139394962631355999178735550317821) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 75 +
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
  rw [recurrence2Scalar3Left_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_182 :
    recurrence2Scalar3Left.coeff 182 =
      -(((221863064333506162807236981203421443049823853001802141571 * 10 ^ 70 +
        1295551138893209537418490612813612093395283336296716976417782178247132) * 10 ^ 70 +
        6456139036167747306379030839152287402747276087412629615269633306724207) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 76 +
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
  rw [recurrence2Scalar3Left_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_183 :
    recurrence2Scalar3Left.coeff 183 =
      (((804164828017363127235597635497664572880544751163332125965 * 10 ^ 70 +
        0885637382871845133321051579277707979601423775920594228260894810186558) * 10 ^ 70 +
        0493588591724412080494679164178600003300470850425532897848524378684438) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 77 +
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
  rw [recurrence2Scalar3Left_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_184 :
    recurrence2Scalar3Left.coeff 184 =
      -(((1425671847700117014294720867653443801758376625329421622175 * 10 ^ 70 +
        3938786220501076567293426136512518226873825802342996778843915312257489) * 10 ^ 70 +
        6244575605409016105574760836216267344727010591444956229143807419512202) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 78 +
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
  rw [recurrence2Scalar3Left_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_185 :
    recurrence2Scalar3Left.coeff 185 =
      -(((482153638534590983617175435671762737022314268337193522341 * 10 ^ 70 +
        0745159908354992598067356745225176727197766859516640751719092767858009) * 10 ^ 70 +
        9315556784812556285112108403320549110169876262000128351858560240133862) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 79 +
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
  rw [recurrence2Scalar3Left_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_186 :
    recurrence2Scalar3Left.coeff 186 =
      (((12313836090897832156557011726420577622180637669689946497142 * 10 ^ 70 +
        7418323376262378508435276327669537117465120114321982145485775942650301) * 10 ^ 70 +
        0769292776265675489292193034638128707284343450705983216413037316173662) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 80 +
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
  rw [recurrence2Scalar3Left_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_187 :
    recurrence2Scalar3Left.coeff 187 =
      -(((44203709569798262383441489807379029446576246737197765105368 * 10 ^ 70 +
        1335350874107270307791090438106763383881427557235837363919121233748963) * 10 ^ 70 +
        0359679474781776427392238117580726650242169290976983966500224551372167) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 81 +
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
  rw [recurrence2Scalar3Left_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_188 :
    recurrence2Scalar3Left.coeff 188 =
      (((84079351629718217126975018744516601785703335270221673301674 * 10 ^ 70 +
        9935402896435265844158454142519502519220334531942940127702129105868753) * 10 ^ 70 +
        2392920549350469922349903852905647678446208216021525042128813558431162) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 82 +
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
  rw [recurrence2Scalar3Left_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_189 :
    recurrence2Scalar3Left.coeff 189 =
      -(((18422394908845200963377118181905805727922185926556892683408 * 10 ^ 70 +
        7522437427181574870557715917764738076260993920575685583455677278489794) * 10 ^ 70 +
        2868635382354483591265665201179338963289064150189173693062768969840313) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 83 +
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
  rw [recurrence2Scalar3Left_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_190 :
    recurrence2Scalar3Left.coeff 190 =
      -(((503204825765916880358215966482166088987782443236866932776551 * 10 ^ 70 +
        8721380988346082010338583630902046659424941301618598397089346060317563) * 10 ^ 70 +
        6367356094044166635204483885695787237220994202565272334784127698903872) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 84 +
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
  rw [recurrence2Scalar3Left_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_191 :
    recurrence2Scalar3Left.coeff 191 =
      (((2076127411424407519283045498940114093362019472703458026155428 * 10 ^ 70 +
        8054602248649652508782279122509308854638333409770987611111307055211819) * 10 ^ 70 +
        4939204890100799802437775670066847298214195167836787515896534830134486) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 85 +
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
  rw [recurrence2Scalar3Left_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_192 :
    recurrence2Scalar3Left.coeff 192 =
      -(((4740016516465735681954618106342473905087002749144995210065335 * 10 ^ 70 +
        0982321432439283246572464528953929416785675621044381496457525127574969) * 10 ^ 70 +
        2017234988136429787894077194511148912110628223197577919059691749186038) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 86 +
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
  rw [recurrence2Scalar3Left_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_193 :
    recurrence2Scalar3Left.coeff 193 =
      (((4958971102841599687613218093887891380138079757847063336135740 * 10 ^ 70 +
        5547452252647748648807866375690118997639620222384744368861461778738710) * 10 ^ 70 +
        7701775251741079592290671675241550985781378646077437856106974279151491) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 87 +
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
  rw [recurrence2Scalar3Left_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_194 :
    recurrence2Scalar3Left.coeff 194 =
      (((10877699015226361862598848364604978194873224522562005911897301 * 10 ^ 70 +
        6507864315812575916348267045635602851495316040995978953123012771659000) * 10 ^ 70 +
        5359611110294182954017648193934559252671180423195167772003875864990825) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 88 +
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
  rw [recurrence2Scalar3Left_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_195 :
    recurrence2Scalar3Left.coeff 195 =
      -(((73178856958939072512004366711072029849449244136783677878588087 * 10 ^ 70 +
        3845788913081636183003985875879772914075678161602716214692563554644540) * 10 ^ 70 +
        0242353085162505972172329540356668425157576871760093298002634607028781) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 89 +
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
  rw [recurrence2Scalar3Left_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_196 :
    recurrence2Scalar3Left.coeff 196 =
      (((217495924206605931383876827477931466858787418521136662638393406 * 10 ^ 70 +
        1187854562204051856085894418305070101933612507591136719777654027268277) * 10 ^ 70 +
        0366494554893519992189399340172740337659763733636906749572992883903626) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 90 +
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
  rw [recurrence2Scalar3Left_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_197 :
    recurrence2Scalar3Left.coeff 197 =
      -(((404515122042726264628653339687635884073322735909466334255176907 * 10 ^ 70 +
        0581539185544549738347145717635414941126779653311441919863421528568671) * 10 ^ 70 +
        5297193937403711287649880093759446226895441769439616039009508359705369) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 91 +
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
  rw [recurrence2Scalar3Left_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_198 :
    recurrence2Scalar3Left.coeff 198 =
      (((287573163175405497175451200946458242278623768494599176960041295 * 10 ^ 70 +
        4066946357562701033336824853697411160605004868540665607197365843889350) * 10 ^ 70 +
        6177742800713570319212138691918788940427343009793909123533304029592929) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 92 +
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
  rw [recurrence2Scalar3Left_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_199 :
    recurrence2Scalar3Left.coeff 199 =
      (((1223516505155803165352763085635717041601932313999418022973504981 * 10 ^ 70 +
        0936693909527475369410646803520732352654290687782475342381149932233958) * 10 ^ 70 +
        7713743853742844405729548100900935651947572014241456213209535883329382) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 93 +
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
  rw [recurrence2Scalar3Left_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_200 :
    recurrence2Scalar3Left.coeff 200 =
      -(((6374597035731691707618123826051929272771278442928298672437063671 * 10 ^ 70 +
        5419800202215632999432377044448580302683383569609196512892383792022570) * 10 ^ 70 +
        9048261135319056243599992011151193562749290452966899623411794556899532) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 94 +
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
  rw [recurrence2Scalar3Left_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_201 :
    recurrence2Scalar3Left.coeff 201 =
      (((17900453232542661986566390065072740470921990593266759186781358059 * 10 ^ 70 +
        1359148255798751165898854425394861153483190601488168723733593239224846) * 10 ^ 70 +
        0813612898264725809286546422455634134948941559288058221317639632850070) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 95 +
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
  rw [recurrence2Scalar3Left_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_202 :
    recurrence2Scalar3Left.coeff 202 =
      -(((34587644042605756211331762217047792246891572873164131075910305064 * 10 ^ 70 +
        5613174072927244344171934215722864917264290817023508763179675045566167) * 10 ^ 70 +
        0733458245679079377017623732775261798345955109194362954211741882964967) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 96 +
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
  rw [recurrence2Scalar3Left_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_203 :
    recurrence2Scalar3Left.coeff 203 =
      (((38285560964705961454276945023849618320740098644954688355280772317 * 10 ^ 70 +
        2210338214938906870090006870737754876773988965032724403813789653568892) * 10 ^ 70 +
        2661450295949604948410789031229344419327276317300163578668894675536678) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 97 +
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
  rw [recurrence2Scalar3Left_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_204 :
    recurrence2Scalar3Left.coeff 204 =
      (((32753808373605642654587346042600764170577016191003378467539657733 * 10 ^ 70 +
        5871074377316116394477460924962448638928745229287267026655089519024658) * 10 ^ 70 +
        1779894635206517565475971237568013989669539522428662614462883244865150) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 98 +
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
  rw [recurrence2Scalar3Left_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_205 :
    recurrence2Scalar3Left.coeff 205 =
      -(((322044599572493349459435680853838758496858912034918178063122393876 * 10 ^ 70 +
        9400395158698691155835258515895330186093138731439429100587165607438091) * 10 ^ 70 +
        4636156281017427634279793293658854916850580985406220375047927828058541) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 99 +
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
  rw [recurrence2Scalar3Left_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_206 :
    recurrence2Scalar3Left.coeff 206 =
      (((1076439547243174890860341562056211700601002235803193758826668744497 * 10 ^ 70 +
        4702009542861772444559421850471201318663397444945091577100057274730933) * 10 ^ 70 +
        3449091755628830082772776518405574208031969272660414662121646868264574) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 100 +
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
  rw [recurrence2Scalar3Left_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_207 :
    recurrence2Scalar3Left.coeff 207 =
      -(((2563303769105782231382905275598812040894774052615008978697658689298 * 10 ^ 70 +
        9440886372261578851496816238135359293057114055532425238178733694677104) * 10 ^ 70 +
        6483215861251367353159910727273265677546744463872352368489636372986101) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 101 +
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
  rw [recurrence2Scalar3Left_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_208 :
    recurrence2Scalar3Left.coeff 208 =
      (((4690372890582882837759177581863947981005515651751342467295617289531 * 10 ^ 70 +
        6412723421877717027393764700605561442515961636074227175294816987562400) * 10 ^ 70 +
        8583659114129006453231583919553483309329206426562141491668109795049042) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 102 +
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
  rw [recurrence2Scalar3Left_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_209 :
    recurrence2Scalar3Left.coeff 209 =
      -(((5994342997198344220908444026473957533790438167126104131679037889917 * 10 ^ 70 +
        9002081599635377340588764564791727453569089162774387515328324738994382) * 10 ^ 70 +
        1569483024294032133142320876291421296533266430847189989736960120726241) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 103 +
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
  rw [recurrence2Scalar3Left_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_210 :
    recurrence2Scalar3Left.coeff 210 =
      (((1546295036431269765094075984610327764636747082621176918581257503543 * 10 ^ 70 +
        4951094271836104648746735858520541174976044607557609509601118168898388) * 10 ^ 70 +
        2320538173438008679088253682712822767475586121695943489745165270161838) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 104 +
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
  rw [recurrence2Scalar3Left_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_211 :
    recurrence2Scalar3Left.coeff 211 =
      (((20633660267231202777650295921258405189275827601006514212046929926142 * 10 ^ 70 +
        0182654878245852373941269530372140805108549471362095952344843175178053) * 10 ^ 70 +
        4975180626580528504739879171255130442254586818332632164331477001951516) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 105 +
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
  rw [recurrence2Scalar3Left_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_212 :
    recurrence2Scalar3Left.coeff 212 =
      -(((84623331349272367417659741974117242775037047386293894171454816185053 * 10 ^ 70 +
        7118140242693606726865873754099190543597761275450603836502718793050201) * 10 ^ 70 +
        9459527109329180734481121083289920620180162093055309209381361632900388) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 106 +
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
  rw [recurrence2Scalar3Left_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_213 :
    recurrence2Scalar3Left.coeff 213 =
      (((231969826721574570985042686702972940431362720014801854622807289603741 * 10 ^ 70 +
        2776197875263420550094452912784307585790966009625363266238969604859266) * 10 ^ 70 +
        3709179884544168677022332526022281565684216292309814883032638831902552) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 107 +
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
  rw [recurrence2Scalar3Left_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_214 :
    recurrence2Scalar3Left.coeff 214 =
      -(((524272565936183315139545469564864207238570473652674861969632763073206 * 10 ^ 70 +
        0708183798095507406540938324288577884217142795004825284210591171812740) * 10 ^ 70 +
        5084236065115033855562520452308269644059337522379319867753387488813721) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 108 +
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
  rw [recurrence2Scalar3Left_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_215 :
    recurrence2Scalar3Left.coeff 215 =
      (((1037133011169919019916550123488444517588263744240001948518561186130993 * 10 ^ 70 +
        8195695251906723961543511481868519338054731747016066682213578674917408) * 10 ^ 70 +
        9652233178598456753528787438965969828060357144616244365760726976672300) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 109 +
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
  rw [recurrence2Scalar3Left_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_216 :
    recurrence2Scalar3Left.coeff 216 =
      -(((1836823839393470265927672978162225732528426146028722502483827656009715 * 10 ^ 70 +
        8930760163575529126224573302756249201605554862787082936529487119958567) * 10 ^ 70 +
        6943287727462092294443703786143495790493961315630393435398396170387178) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 110 +
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
  rw [recurrence2Scalar3Left_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_217 :
    recurrence2Scalar3Left.coeff 217 =
      (((2929593186358274839608540574857125548500100888502489841024429802890803 * 10 ^ 70 +
        6680084797745707869987643886514920155125228297342651069417559430617499) * 10 ^ 70 +
        5855773655774657603507082917719621011475298828342703011587749312492459) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 111 +
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
  rw [recurrence2Scalar3Left_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_218 :
    recurrence2Scalar3Left.coeff 218 =
      -(((4175516073099543405988764636651511178188096870989736646180577059507268 * 10 ^ 70 +
        2842360040068889832517942008849125653619346108363634272277408015350686) * 10 ^ 70 +
        1958881596240635090147682158402111625325292520013637402578146274544583) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 112 +
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
  rw [recurrence2Scalar3Left_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_219 :
    recurrence2Scalar3Left.coeff 219 =
      (((5166347002885056999871461016635850076502373679296507502962913185601729 * 10 ^ 70 +
        7542646227295638626888521096472398281926500476497252398230932545603599) * 10 ^ 70 +
        9495762640470964743939673460938211987595695326417358497438761735534436) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 113 +
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
  rw [recurrence2Scalar3Left_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_220 :
    recurrence2Scalar3Left.coeff 220 =
      -(((5080976225576140416604125185948372489646449771376614589703027871296282 * 10 ^ 70 +
        8985149156468680185554127391796835721928575735325397065702151438031091) * 10 ^ 70 +
        8873394715164793157326756429013784062781754126856591907802883699108805) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 114 +
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
  rw [recurrence2Scalar3Left_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_221 :
    recurrence2Scalar3Left.coeff 221 =
      (((2551510481048550534606189079548737317640637770207274197361238765632801 * 10 ^ 70 +
        3798076909110150809326400941594181018187600960972410897272305010092173) * 10 ^ 70 +
        0093143482948105416286532016689755861648530929257367541867263431945150) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 115 +
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
  rw [recurrence2Scalar3Left_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_222 :
    recurrence2Scalar3Left.coeff 222 =
      (((4407067737681488604547761961191611789270612456961679326049785845644542 * 10 ^ 70 +
        7020119356399664001158744997433504056686345050208676728318022415993311) * 10 ^ 70 +
        3888612892147513058792421771006938876909717036772377736143217149357556) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 116 +
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
  rw [recurrence2Scalar3Left_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_223 :
    recurrence2Scalar3Left.coeff 223 =
      -((((1 * 10 ^ 70 +
        8338350572577790127136387774287903991314461788202072726916185977677852) * 10 ^ 70 +
        5426853360412256961961687912300642158205832194339516314411314445976827) * 10 ^ 70 +
        8335579350417423921454839148616585882661773860549370259606801352575314) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 117 +
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
  rw [recurrence2Scalar3Left_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_224 :
    recurrence2Scalar3Left.coeff 224 =
      ((((4 * 10 ^ 70 +
        2096582184840600871170530370871669348307593915550997725794500109902158) * 10 ^ 70 +
        0991437157072596985960340144322458093037060739405607817762392951645479) * 10 ^ 70 +
        9104643083076232313524007896084848941025058506071593778759222499045295) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 118 +
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
  rw [recurrence2Scalar3Left_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_225 :
    recurrence2Scalar3Left.coeff 225 =
      -((((7 * 10 ^ 70 +
        8378449922655530716721485057121098384452960145759616407426825405412980) * 10 ^ 70 +
        5077748133669114631439900744331773728053792293595906751102923170874982) * 10 ^ 70 +
        7775349863561930849123967734999730856423013238354151131493490436780769) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 119 +
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
  rw [recurrence2Scalar3Left_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_226 :
    recurrence2Scalar3Left.coeff 226 =
      ((((12 * 10 ^ 70 +
        9059036281384068438293571149933138857365766049526651627072739146838999) * 10 ^ 70 +
        4496537123728190837750029109027422953011336989037460580050437253276202) * 10 ^ 70 +
        8476062279957931146293180190432012130684462704437544931120517743661290) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 120 +
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
  rw [recurrence2Scalar3Left_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_227 :
    recurrence2Scalar3Left.coeff 227 =
      -((((19 * 10 ^ 70 +
        4428562507529442144852294126991473117667961233412694329746079809753237) * 10 ^ 70 +
        5542338295034303220325017788438997479162150204877583209539623298954940) * 10 ^ 70 +
        3518210876526246878708196404333968568439457977474545924787971373854672) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 121 +
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
  rw [recurrence2Scalar3Left_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_228 :
    recurrence2Scalar3Left.coeff 228 =
      ((((27 * 10 ^ 70 +
        2496113842970695387308025306533868962834229517293822797119116712492894) * 10 ^ 70 +
        3200403598442786745149312001326869242271529682515406911385417932770762) * 10 ^ 70 +
        0940458606822632212422215426617001416293374031805870697389440513476515) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 122 +
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
  rw [recurrence2Scalar3Left_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_229 :
    recurrence2Scalar3Left.coeff 229 =
      -((((35 * 10 ^ 70 +
        8567583539444707991236080546864842879813083882898707362072063534466279) * 10 ^ 70 +
        9152598683735344172911490959446873117728372980392826881394275017471586) * 10 ^ 70 +
        7077645428309867303961647823488322177790485492208204716279168393937880) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 123 +
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
  rw [recurrence2Scalar3Left_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_230 :
    recurrence2Scalar3Left.coeff 230 =
      ((((44 * 10 ^ 70 +
        5293600164337820276125087012375970645096872185225016298836517611404647) * 10 ^ 70 +
        3889807609615151814506193179366646599939473237723816007547002245342573) * 10 ^ 70 +
        3294572321614508903010427608719150582222144620835192582054519619143012) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 124 +
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
  rw [recurrence2Scalar3Left_coeff_230_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
