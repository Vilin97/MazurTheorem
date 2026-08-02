/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Left coefficient convolution

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
  recurrence2A4_coeff_0
  recurrence2A4_coeff_1
  recurrence2A4_coeff_2
  recurrence2A4_coeff_3
  recurrence2A4_coeff_4
  recurrence2A4_coeff_5
  recurrence2A4_coeff_6
  recurrence2A4_coeff_7
  recurrence2A4_coeff_8
  recurrence2A4_coeff_9
  recurrence2A4_coeff_10
  recurrence2A4_coeff_11
  recurrence2A4_coeff_12
  recurrence2A4_coeff_13
  recurrence2A4_coeff_14
  recurrence2A4_coeff_15
  recurrence2A4_coeff_16
  recurrence2A4_coeff_17
  recurrence2A4_coeff_18
  recurrence2A4_coeff_19
  recurrence2A4_coeff_20
  recurrence2A4_coeff_21
  recurrence2A4_coeff_22
  recurrence2A4_coeff_23
  recurrence2A4_coeff_24
  recurrence2A4_coeff_25
  recurrence2A4_coeff_26
  recurrence2A4_coeff_27
  recurrence2A4_coeff_28
  recurrence2A4_coeff_29
  recurrence2A4_coeff_30
  recurrence2A4_coeff_31
  recurrence2A4_coeff_32
  recurrence2A4_coeff_33
  recurrence2A4_coeff_34
  recurrence2A4_coeff_35
  recurrence2A4_coeff_36
  recurrence2A4_coeff_37
  recurrence2A4_coeff_38
  recurrence2A4_coeff_39
  recurrence2A4_coeff_40
  recurrence2A4_coeff_41
  recurrence2A4_coeff_42
  recurrence2A4_coeff_43
  recurrence2A4_coeff_44
  recurrence2A4_coeff_45
  recurrence2A4_coeff_46
  recurrence2A4_coeff_47
  recurrence2A4_coeff_48
  recurrence2A4_coeff_49
  recurrence2A4_coeff_50
  recurrence2A4_coeff_51
  recurrence2A4_coeff_52
  recurrence2A4_coeff_53
  recurrence2A4_coeff_54
  recurrence2A4_coeff_55
  recurrence2A4_coeff_56
  recurrence2A4_coeff_57
  recurrence2A4_coeff_58
  recurrence2A4_coeff_59
  recurrence2A4_coeff_60
  recurrence2A4_coeff_61
  recurrence2A4_coeff_62
  recurrence2A4_coeff_63
  recurrence2A4_coeff_64
  recurrence2A4_coeff_65
  recurrence2A4_coeff_66
  recurrence2A4_coeff_67
  recurrence2A4_coeff_68
  recurrence2A4_coeff_69
  recurrence2A4_coeff_70
  recurrence2A4_coeff_71
  recurrence2A4_coeff_72
  recurrence2A4_coeff_73
  recurrence2A4_coeff_74
  recurrence2A4_coeff_75
  recurrence2A4_coeff_76
  recurrence2A4_coeff_77
  recurrence2A4_coeff_78
  recurrence2A4_coeff_79
  recurrence2A4_coeff_80
  recurrence2A4_coeff_81
  recurrence2A4_coeff_82
  recurrence2A4_coeff_83
  recurrence2A4_coeff_84
  recurrence2A4_coeff_85
  recurrence2A4_coeff_86
  recurrence2A4_coeff_87
  recurrence2A4_coeff_88
  recurrence2A4_coeff_89
  recurrence2A4_coeff_90
  recurrence2A4_coeff_91
  recurrence2A4_coeff_92
  recurrence2A4_coeff_93
  recurrence2A4_coeff_94
  recurrence2A4_coeff_95
  recurrence2A4_coeff_96
  recurrence2A4_coeff_97
  recurrence2A4_coeff_98
  recurrence2A4_coeff_99
  recurrence2A4_coeff_100
  recurrence2A4_coeff_101
  recurrence2A4_coeff_102

theorem recurrence2Scalar4Left_coeff_0 :
    recurrence2Scalar4Left.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_1 :
    recurrence2Scalar4Left.coeff 1 =
      (-18366464 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_2 :
    recurrence2Scalar4Left.coeff 2 =
      (14530086912 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_3 :
    recurrence2Scalar4Left.coeff 3 =
      (-766587916917312 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_4 :
    recurrence2Scalar4Left.coeff 4 =
      (757930263587697488 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_5 :
    recurrence2Scalar4Left.coeff 5 =
      (-8192565365708897999792 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_6 :
    recurrence2Scalar4Left.coeff 6 =
      (9571465177509678944820708 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_7 :
    recurrence2Scalar4Left.coeff 7 =
      (-4212720997200249201376329308 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_8 :
    recurrence2Scalar4Left.coeff 8 =
      (2182234416428656503813690444804 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_9 :
    recurrence2Scalar4Left.coeff 9 =
      (2522230300718545608472549008084708 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_10 :
    recurrence2Scalar4Left.coeff 10 =
      (-2259772546827178102110765746928712020 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_11 :
    recurrence2Scalar4Left.coeff 11 =
      (1757444103469940677750956939858126896068 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_12 :
    recurrence2Scalar4Left.coeff 12 =
      (-838773136328525888861711226233956367470276 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_13 :
    recurrence2Scalar4Left.coeff 13 =
      (286447461256660862550398310817790198215884320 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_14 :
    recurrence2Scalar4Left.coeff 14 =
      (-72923860842659462023346248040749270180659487424 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_15 :
    recurrence2Scalar4Left.coeff 15 =
      (14225210992610214170122632118618988267747782657360 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_16 :
    recurrence2Scalar4Left.coeff 16 =
      (-2166665403988461880674105296517250143283857430249759 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_17 :
    recurrence2Scalar4Left.coeff 17 =
      (256844580681913182802790885426529779937616834726969103 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_18 :
    recurrence2Scalar4Left.coeff 18 =
      (-23430702017616767049471792857469124382796049633144194910 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_19 :
    recurrence2Scalar4Left.coeff 19 =
      (1576670171102617405145499229608703461206148315810353471742 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_20 :
    recurrence2Scalar4Left.coeff 20 =
      (-68103763373302658199272942793891232198813260624059635503571 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_21 :
    recurrence2Scalar4Left.coeff 21 =
      (463556092563538155467063618731935082607760207513827681568542 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_22 :
    recurrence2Scalar4Left.coeff 22 =
      (212077828412794900708209573518363154141900991034532985454709394 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_23 :
    recurrence2Scalar4Left.coeff 23 =
      (-21563634934583553774872246322045742082573292593045303297413171139 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_24 :
    recurrence2Scalar4Left.coeff 24 =
      (1333282281365816240105459835853696820079876161584762611236831563547 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_25 :
    recurrence2Scalar4Left.coeff 25 =
      (-60807583974362519645261544810082714888439405592432915023027555597115 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_26 :
    recurrence2Scalar4Left.coeff 26 =
      (2013248388204667552906846551827887535812692456423544555763911021054225 : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_27 :
    recurrence2Scalar4Left.coeff 27 =
      -((2 * 10 ^ 70 +
        8986439423828736442110284169221325278527573123114133995972528076145794) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_28 :
    recurrence2Scalar4Left.coeff 28 =
      -((219 * 10 ^ 70 +
        8965918132177172132082250894233577846775941695429538913394488089906654) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_29 :
    recurrence2Scalar4Left.coeff 29 =
      ((24108 * 10 ^ 70 +
        9234579868217336148394543364856094166008303690683840931012286092449629) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_30 :
    recurrence2Scalar4Left.coeff 30 =
      -((1408553 * 10 ^ 70 +
        2378014761901078974387330247992022158452352463151475115238898772772753) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_31 :
    recurrence2Scalar4Left.coeff 31 =
      ((58823933 * 10 ^ 70 +
        0154974858633850563692511011982018717561367361381028821398311436237835) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_32 :
    recurrence2Scalar4Left.coeff 32 =
      -((1780648013 * 10 ^ 70 +
        2611747409626184656588103682290689221198567340303779096603379010227739) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_33 :
    recurrence2Scalar4Left.coeff 33 =
      ((30134985660 * 10 ^ 70 +
        0126353924168788188951458650196845207550945473587614074878449319270125) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_34 :
    recurrence2Scalar4Left.coeff 34 =
      ((655364427484 * 10 ^ 70 +
        0444569516868842022325174195832552171819661956300107204810584625603566) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_35 :
    recurrence2Scalar4Left.coeff 35 =
      -((89696341495680 * 10 ^ 70 +
        2207694183813309396743050674237108893482257157405605223359026646365163) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_36 :
    recurrence2Scalar4Left.coeff 36 =
      ((5019814753525830 * 10 ^ 70 +
        7317034388221932694505695688552855551609957988663134956460776351731082) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_37 :
    recurrence2Scalar4Left.coeff 37 =
      -((199368843359121784 * 10 ^ 70 +
        9977652421264249610583544319262247295787073541384799382810622190187490) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_38 :
    recurrence2Scalar4Left.coeff 38 =
      ((5895326800941292117 * 10 ^ 70 +
        6879268733586991591577162716296336997734894236036102860521606066865127) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_39 :
    recurrence2Scalar4Left.coeff 39 =
      -((117030100343280354936 * 10 ^ 70 +
        2515549257020526698602540317679570767219933508003283892752348380765270) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_40 :
    recurrence2Scalar4Left.coeff 40 =
      ((499005196038419342018 * 10 ^ 70 +
        4170517570199162786169524987120085072340091290210659277813146054393497) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_41 :
    recurrence2Scalar4Left.coeff 41 =
      ((80833446280423561797157 * 10 ^ 70 +
        7362622286688572225948317898240325053252519628162058565546197175149601) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_42 :
    recurrence2Scalar4Left.coeff 42 =
      -((4634419049988368744655188 * 10 ^ 70 +
        5033053160838156415702704440173041232413471013816907576007095662673355) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_43 :
    recurrence2Scalar4Left.coeff 43 =
      ((175297643615179704140275767 * 10 ^ 70 +
        5242732929426214177951911112327807843733894564914982933441164667554473) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_44 :
    recurrence2Scalar4Left.coeff 44 =
      -((5543051820028558968847251855 * 10 ^ 70 +
        1771771814937978653917490282321665083603552356272986993810778698313456) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_45 :
    recurrence2Scalar4Left.coeff 45 =
      ((157910760567086430038781225143 * 10 ^ 70 +
        9261775352503345110090550347086834672432167101359008481377277080807293) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_46 :
    recurrence2Scalar4Left.coeff 46 =
      -((4159057175286965550827200143121 * 10 ^ 70 +
        2926771075769229406420557495365992954984625820825936084126092967455717) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_47 :
    recurrence2Scalar4Left.coeff 47 =
      ((101399590812515289185476229359571 * 10 ^ 70 +
        7408971919102211087421523591420020348637617931659126143324164401139110) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_48 :
    recurrence2Scalar4Left.coeff 48 =
      -((2265291884852132627402505400221095 * 10 ^ 70 +
        4796977560588440404197598694298174671097613700548592570859634571886991) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_49 :
    recurrence2Scalar4Left.coeff 49 =
      ((45714549737470130831468626779449967 * 10 ^ 70 +
        9950739562764966502534653630886424835895236208804422416822153986778689) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_50 :
    recurrence2Scalar4Left.coeff 50 =
      -((818513967386699179029688236377472048 * 10 ^ 70 +
        8925538353956947665156342926069218866588714906110080440418012409918444) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_51 :
    recurrence2Scalar4Left.coeff 51 =
      ((12627826242785478045667504706484551955 * 10 ^ 70 +
        6429604983498427958578929737566587382011899048678590875384719356694394) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_52 :
    recurrence2Scalar4Left.coeff 52 =
      -((156819616353213802862358173642913345703 * 10 ^ 70 +
        6431055561652685934022819262256336206134589741413424048678939194452340) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_53 :
    recurrence2Scalar4Left.coeff 53 =
      ((1208633110943457278846296325981627106582 * 10 ^ 70 +
        4174592361085376410955379640167564973009982272832362797650071035304620) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_54 :
    recurrence2Scalar4Left.coeff 54 =
      ((7562790878416542496328751633792260192045 * 10 ^ 70 +
        7291502947604900057701602493416047102830506586717084787569968647857737) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_55 :
    recurrence2Scalar4Left.coeff 55 =
      -((567185960810854824895431611626428888858577 * 10 ^ 70 +
        6726918630618915314584256991189916419954736088887222426388484574037069) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_56 :
    recurrence2Scalar4Left.coeff 56 =
      ((15021353045865382119845439130478587096206858 * 10 ^ 70 +
        6257980136819028008794762552647535548244932109413308021072987193664252) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_57 :
    recurrence2Scalar4Left.coeff 57 =
      -((297703767789669991649003069175028176567301119 * 10 ^ 70 +
        5172867621223179642375491468704460695487910214510910213609604584033066) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_58 :
    recurrence2Scalar4Left.coeff 58 =
      ((4929645260551758591686918307384108652939991068 * 10 ^ 70 +
        1688853034947744488248370141848794068015206131453660055768553156081188) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_59 :
    recurrence2Scalar4Left.coeff 59 =
      -((70099177609659576686252366912052886211757468128 * 10 ^ 70 +
        4509905662518242151847146224009093358440499605330194268774845421334187) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_60 :
    recurrence2Scalar4Left.coeff 60 =
      ((847671373781160556385946520086936527354257281881 * 10 ^ 70 +
        6666838705068044803575012958233211596351440187461351047866293291933651) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_61 :
    recurrence2Scalar4Left.coeff 61 =
      -((8186382222859420488712542623456079336624899449959 * 10 ^ 70 +
        4527755234564256629937648779798751147232458823832041993475900625336087) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_62 :
    recurrence2Scalar4Left.coeff 62 =
      ((47306780163745908574724892086246897929382684507016 * 10 ^ 70 +
        9603742459839271595226157618640881203160851781425420583572975531892702) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_63 :
    recurrence2Scalar4Left.coeff 63 =
      ((326263829585230058557581311156470085386374223058714 * 10 ^ 70 +
        7953198908602351359922887435038394377476197392679434952485804719314655) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_64 :
    recurrence2Scalar4Left.coeff 64 =
      -((16720618914622408723066293319398545787966217221584634 * 10 ^ 70 +
        4832928123859413972621189232568228362324649384284509771773834950522064) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_65 :
    recurrence2Scalar4Left.coeff 65 =
      ((357234593989662243724486898876736216275639292088753457 * 10 ^ 70 +
        4807229984723324734819049837876512960314944597013022834793983314277519) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_66 :
    recurrence2Scalar4Left.coeff 66 =
      -((5925166687153367775248417747319476261974032035014188266 * 10 ^ 70 +
        0753934650541441846395764779058980189210799186023130620869230681858029) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_67 :
    recurrence2Scalar4Left.coeff 67 =
      ((85194920489177093459538884521126603613996091867940527833 * 10 ^ 70 +
        9475746905653441633527642275090390445945190603489074423386763659080320) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_68 :
    recurrence2Scalar4Left.coeff 68 =
      -((1106592673422591030275754224577269956321925124826899863956 * 10 ^ 70 +
        1572821862663696498026816092646257654494911957648352018900803676236598) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_69 :
    recurrence2Scalar4Left.coeff 69 =
      ((13251165073357879851148625970204280431101173787338299108914 * 10 ^ 70 +
        3949456067820255133916038766419731126498699334780064890820890221980591) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_70 :
    recurrence2Scalar4Left.coeff 70 =
      -((148018036205260394701837316605554205814152021655536575207078 * 10 ^ 70 +
        9017236973142252320254999409577528977306061819107321096530450855753577) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_71 :
    recurrence2Scalar4Left.coeff 71 =
      ((1553961763702209444216274667947875511823126448361876312953384 * 10 ^ 70 +
        4494931082092341938085191887182762125030457819743044140021138669475547) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_72 :
    recurrence2Scalar4Left.coeff 72 =
      -((15413148240547630375768530690775037525471258453857581768219308 * 10 ^ 70 +
        0838187368981096205844925887745075281851793038118094201181742273642371) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_73 :
    recurrence2Scalar4Left.coeff 73 =
      ((144984078371076915950435719825304020879519265176819758171548844 * 10 ^ 70 +
        0056367194326432726862036194845301243949535538280036342187852196539870) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_74 :
    recurrence2Scalar4Left.coeff 74 =
      -((1297142686599829014867246999146187516635950977630280406197511888 * 10 ^ 70 +
        4472310054112509609478605764636193838323830805851313927558834933745401) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_75 :
    recurrence2Scalar4Left.coeff 75 =
      ((11063306293503269831160427659071006111540883012164021915318625007 * 10 ^ 70 +
        3147701519058705250556261306842645699964456426994065932113510422479533) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_76 :
    recurrence2Scalar4Left.coeff 76 =
      -((90117211332298513137489195726344261056893215281903015576578068604 * 10 ^ 70 +
        8669642416485590013301720187969969402400897659253070098317944051262283) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_77 :
    recurrence2Scalar4Left.coeff 77 =
      ((702108175503203978499206708927134470142067406119668600427284583876 * 10 ^ 70 +
        6385130335379197271390925763279710567794520399209121167614888774024727) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_78 :
    recurrence2Scalar4Left.coeff 78 =
      -((5238490021645901434433772507484263254661869703394361264077681251374 * 10 ^ 70 +
        6215262125950286349176390192447370629054132332535079778869743008238959) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_79 :
    recurrence2Scalar4Left.coeff 79 =
      ((37467463804797816496775020832147555178935655096452248360876686794589 * 10 ^ 70 +
        5310691773533876858148313934221204817675599227406770490146330083981969) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_80 :
    recurrence2Scalar4Left.coeff 80 =
      -((257106964558488542312954964430126928934701236314822672477526631502490 * 10 ^ 70 +
        7131059366131392488544407564446479385167917193095159682199914430699847) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_81 :
    recurrence2Scalar4Left.coeff 81 =
      ((1693895385799078221440858661547773364314750665507129686356857334005949 * 10 ^ 70 +
        1060873772566704149382404751371140355255038256131097020630836661183342) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_82 :
    recurrence2Scalar4Left.coeff 82 =
      -(((1 * 10 ^ 70 +
        0720555808862915651047778512998384040691388914887209578747263234228881) * 10 ^ 70 +
        5200903346980499695892961339094369271736387895429261280837386265405389) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_83 :
    recurrence2Scalar4Left.coeff 83 =
      (((6 * 10 ^ 70 +
        5207193824539433741292617907912889407978046004339520107548506320019279) * 10 ^ 70 +
        1807080647500018910692556142044656190093367176657002838544355471254923) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_84 :
    recurrence2Scalar4Left.coeff 84 =
      -(((38 * 10 ^ 70 +
        1288515378118517554508472123113108118457580113675944813687202493019115) * 10 ^ 70 +
        2805675364766482132290205970533595765855565283609535515019469978325339) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_85 :
    recurrence2Scalar4Left.coeff 85 =
      (((214 * 10 ^ 70 +
        3697828050315527606498741228852274732319188100337870768764326355803816) * 10 ^ 70 +
        7029120829415827634823499411964806517233979973679384795519776371911964) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_86 :
    recurrence2Scalar4Left.coeff 86 =
      -(((1158 * 10 ^ 70 +
        8601194924718108295650632249945175199715312795196984387755988169047757) * 10 ^ 70 +
        5454506359993429095648849574776395044633714531119533688032049434651954) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_87 :
    recurrence2Scalar4Left.coeff 87 =
      (((6022 * 10 ^ 70 +
        6963623452124263460047940823289445462679081138948060351614734779204042) * 10 ^ 70 +
        8096099316293865643980934250050140259137779906009771232781629042666857) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_88 :
    recurrence2Scalar4Left.coeff 88 =
      -(((30081 * 10 ^ 70 +
        4966460481797082615588067743579432274001939637142057766392531763486302) * 10 ^ 70 +
        2460948193375347641438046870305447481670278327632443335058227315534431) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_89 :
    recurrence2Scalar4Left.coeff 89 =
      (((144317 * 10 ^ 70 +
        5922511039527020472348498607943248158643727743058097888233760535366928) * 10 ^ 70 +
        3238181497321623225395342585046093354647089132487895262417491953754494) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_90 :
    recurrence2Scalar4Left.coeff 90 =
      -(((664496 * 10 ^ 70 +
        7701043297331545868301708226480686112808475340091487181811584393833257) * 10 ^ 70 +
        8123885060643387070938964422481878061023868328334145265560447426714359) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_91 :
    recurrence2Scalar4Left.coeff 91 =
      (((2932876 * 10 ^ 70 +
        8700021393984013774246021668053376491510961578308269018188713768494381) * 10 ^ 70 +
        4753203148809989603108690707519656363484254327090231087025547229961466) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_92 :
    recurrence2Scalar4Left.coeff 92 =
      -(((12386482 * 10 ^ 70 +
        4177527357057794655028943003792375381717281835983967451089516109893981) * 10 ^ 70 +
        4894284263082841815965889223468718979131325106391780161410265857446284) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_93 :
    recurrence2Scalar4Left.coeff 93 =
      (((49924199 * 10 ^ 70 +
        6813327601432781398839731143336455233956867282867382387948216334940608) * 10 ^ 70 +
        8386161807965431025562731885130051353424813043753494108102881866767308) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_94 :
    recurrence2Scalar4Left.coeff 94 =
      -(((191283669 * 10 ^ 70 +
        1726024791563070804498916001341752493006595265217465252937195585535497) * 10 ^ 70 +
        7309096050330261335023869478030955596102193724084505623773278148872298) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_95 :
    recurrence2Scalar4Left.coeff 95 =
      (((692562248 * 10 ^ 70 +
        8264816458393518809017665738725991074551049663282781449341722324599238) * 10 ^ 70 +
        7035571588580587992168253947547792113903512696409624985597122377426341) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_96 :
    recurrence2Scalar4Left.coeff 96 =
      -(((2347207580 * 10 ^ 70 +
        5742551967935295168824217951080802254208324845005617354115454940852727) * 10 ^ 70 +
        6874176197083842218235380068565371759660927330692414888813784021464144) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_97 :
    recurrence2Scalar4Left.coeff 97 =
      (((7326617187 * 10 ^ 70 +
        7583327569027614213828344517862689740036291590684713037907639961957600) * 10 ^ 70 +
        2448922415697601430716456783779427529333078311970499416222165128260647) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_98 :
    recurrence2Scalar4Left.coeff 98 =
      -(((20397217374 * 10 ^ 70 +
        2421320164488604025258517329451743451785601266055605642842020914284586) * 10 ^ 70 +
        1856230906351554834757236406686610939971542776421790120889261079109845) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_99 :
    recurrence2Scalar4Left.coeff 99 =
      (((46723266417 * 10 ^ 70 +
        4554531396645250297647272410426422615765593780564179907770470639618543) * 10 ^ 70 +
        2003264309475901192677569171796731314370644899398117764137041731478895) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_100 :
    recurrence2Scalar4Left.coeff 100 =
      -(((62406636414 * 10 ^ 70 +
        7089224815362462078108856635390129140634894529368471798532382730439659) * 10 ^ 70 +
        7676646961359804713869735568894030849049533827489440880974778548263166) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_101 :
    recurrence2Scalar4Left.coeff 101 =
      -(((154329546821 * 10 ^ 70 +
        6450531341553683009346789850629935408872183863185219971824617176695712) * 10 ^ 70 +
        8847526866718103006751987168470596703463002355142365872293867505790743) : ℚ) := by
  unfold recurrence2Scalar4Left
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

theorem recurrence2Scalar4Left_coeff_102 :
    recurrence2Scalar4Left.coeff 102 =
      (((1783587597340 * 10 ^ 70 +
        8902600963390413939509447581687174642745918373766164584597188494369799) * 10 ^ 70 +
        9416263719595859003653093941487009989793674918898402173393690128616628) : ℚ) := by
  unfold recurrence2Scalar4Left
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

private theorem recurrence2Scalar4Left_coeff_103_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (103 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (103 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_103 :
    recurrence2Scalar4Left.coeff 103 =
      -(((9937276052513 * 10 ^ 70 +
        0276520081574506416641215406432296345499069517160872416385394619561219) * 10 ^ 70 +
        7962905632572096570272861648651402800360655365732884878924666562214559) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 104 = 1 +
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
  rw [recurrence2Scalar4Left_coeff_103_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_104_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (104 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (104 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_104 :
    recurrence2Scalar4Left.coeff 104 =
      (((44005775233064 * 10 ^ 70 +
        1352184713371900677215361934020669208291326003894416581465151047943686) * 10 ^ 70 +
        6192626688461385179281864274805263426408501325683273106808793919307410) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 105 = 2 +
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
  rw [recurrence2Scalar4Left_coeff_104_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_105_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (105 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (105 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_105 :
    recurrence2Scalar4Left.coeff 105 =
      -(((169589339732919 * 10 ^ 70 +
        9098049032697166432347255046240617061235938304222118135614027806645024) * 10 ^ 70 +
        0084973526183932413199788693015288198161632968974997168582555211280076) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 106 = 3 +
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
  rw [recurrence2Scalar4Left_coeff_105_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_106_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (106 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (106 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_106 :
    recurrence2Scalar4Left.coeff 106 =
      (((583967038931294 * 10 ^ 70 +
        8123646086556281231412682490533573311700026623139452848787071986238268) * 10 ^ 70 +
        4558787145733485455761192866826452932191432575798073585511160577176727) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 107 = 4 +
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
  rw [recurrence2Scalar4Left_coeff_106_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_107_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (107 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (107 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_107 :
    recurrence2Scalar4Left.coeff 107 =
      -(((1807359447335394 * 10 ^ 70 +
        3994006914691517810499472738668479626353297382861133591878172874928517) * 10 ^ 70 +
        5286349189886208261949380909884233276968704619458519320373871575165381) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 108 = 5 +
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
  rw [recurrence2Scalar4Left_coeff_107_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_108_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (108 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (108 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_108 :
    recurrence2Scalar4Left.coeff 108 =
      (((5038569563880457 * 10 ^ 70 +
        1037340573208384315390800867810834495187509892288930885341583143051585) * 10 ^ 70 +
        2486831883821657514720242338810227671340866142244016042281695735981756) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 109 = 6 +
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
  rw [recurrence2Scalar4Left_coeff_108_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_109_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (109 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (109 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_109 :
    recurrence2Scalar4Left.coeff 109 =
      -(((12892136418236667 * 10 ^ 70 +
        0318346683467111814175845531794745019769079893283158054615400810883630) * 10 ^ 70 +
        8997529525966517845622849139519313247616491368879544026268392047392382) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 110 = 7 +
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
  rw [recurrence2Scalar4Left_coeff_109_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_110_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (110 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (110 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_110 :
    recurrence2Scalar4Left.coeff 110 =
      (((32298720992951532 * 10 ^ 70 +
        5773566256223815978128624923106724558689189706461488797120233116433374) * 10 ^ 70 +
        3137735456950770448424478430071239137542896812695929199608508510241662) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 111 = 8 +
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
  rw [recurrence2Scalar4Left_coeff_110_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_111_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (111 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (111 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_111 :
    recurrence2Scalar4Left.coeff 111 =
      -(((86286244830624092 * 10 ^ 70 +
        3425672512970892469661225372967053039463021642586835548113194908663573) * 10 ^ 70 +
        2818265801211379297964745053712681114591147187634145925294247786426436) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 112 = 9 +
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
  rw [recurrence2Scalar4Left_coeff_111_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_112_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (112 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (112 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_112 :
    recurrence2Scalar4Left.coeff 112 =
      (((226152889126670595 * 10 ^ 70 +
        6410226460207183119365299120594465724953143000507650061958721209658748) * 10 ^ 70 +
        7632854101603336193021639088286593225344043132265910827662733474927517) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 113 = 10 +
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
  rw [recurrence2Scalar4Left_coeff_112_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_113_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (113 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (113 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_113 :
    recurrence2Scalar4Left.coeff 113 =
      -(((299845404441476839 * 10 ^ 70 +
        1707119966342592155221177417444779068650143906209113660542246567545150) * 10 ^ 70 +
        5157539088651256374191133204510742546529011908263066911400007186804328) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 114 = 11 +
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
  rw [recurrence2Scalar4Left_coeff_113_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_114_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (114 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (114 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_114 :
    recurrence2Scalar4Left.coeff 114 =
      -(((1970442017415426741 * 10 ^ 70 +
        2504502907226847610938962767913817672425747236952865803905954019231539) * 10 ^ 70 +
        3192015557332355423629711172121982610448622870218244614549380192775596) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 115 = 12 +
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
  rw [recurrence2Scalar4Left_coeff_114_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_115_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (115 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (115 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_115 :
    recurrence2Scalar4Left.coeff 115 =
      (((19034235499761657915 * 10 ^ 70 +
        0654165797022196665585253867859813817263296406714486693068036303738047) * 10 ^ 70 +
        5591619060056354087393531221093810312214901660622898347821662945535972) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 116 = 13 +
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
  rw [recurrence2Scalar4Left_coeff_115_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_116_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (116 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (116 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_116 :
    recurrence2Scalar4Left.coeff 116 =
      -(((90381237928145533599 * 10 ^ 70 +
        0197947491952711954810846295787087214291015779629247809241682748155447) * 10 ^ 70 +
        8585532466299386726250570778217162209470339506455173687941335794060983) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 117 = 14 +
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
  rw [recurrence2Scalar4Left_coeff_116_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_117_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (117 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (117 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_117 :
    recurrence2Scalar4Left.coeff 117 =
      (((262735444214392529498 * 10 ^ 70 +
        4857010444277391575961768614823891195557536092274110418458438463667551) * 10 ^ 70 +
        3108232155602977864098582456667007977648268814014734291631715007808569) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 118 = 15 +
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
  rw [recurrence2Scalar4Left_coeff_117_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_118_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (118 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (118 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_118 :
    recurrence2Scalar4Left.coeff 118 =
      -(((272841493072263858046 * 10 ^ 70 +
        3500979670752361795460253040798072692152914394374528279010752658919477) * 10 ^ 70 +
        9140426849690351622054192808486947016268786950612884679324771667424142) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 119 = 16 +
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
  rw [recurrence2Scalar4Left_coeff_118_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_119_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (119 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (119 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_119 :
    recurrence2Scalar4Left.coeff 119 =
      -(((1813436841870717019310 * 10 ^ 70 +
        1910094346638153951345474429265052518650475033007081078797083235121567) * 10 ^ 70 +
        5034061333069825004049412881896585156241350973752909184479409997515031) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 120 = 17 +
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
  rw [recurrence2Scalar4Left_coeff_119_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_120_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (120 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (120 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_120 :
    recurrence2Scalar4Left.coeff 120 =
      (((12513019137563323165051 * 10 ^ 70 +
        7856411364675009458947594065989670443602269652690132740527058746179855) * 10 ^ 70 +
        1536649943727711015011195431687941903039452627065909219377635572902621) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 121 = 18 +
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
  rw [recurrence2Scalar4Left_coeff_120_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_121_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (121 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (121 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_121 :
    recurrence2Scalar4Left.coeff 121 =
      -(((39277927190620584597949 * 10 ^ 70 +
        7206016974092560528649107905972849539681561886057332597349036987166749) * 10 ^ 70 +
        1720915757251579166780343438225319389046648707048560599583486767965782) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 122 = 19 +
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
  rw [recurrence2Scalar4Left_coeff_121_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_122_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (122 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (122 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_122 :
    recurrence2Scalar4Left.coeff 122 =
      (((24934197720162022649988 * 10 ^ 70 +
        0637188129436850516546545727194651010891792436594104954621832332583553) * 10 ^ 70 +
        6646512775268353775786030101399818295287562084849044240456559598615461) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 123 = 20 +
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
  rw [recurrence2Scalar4Left_coeff_122_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_123_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (123 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (123 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_123 :
    recurrence2Scalar4Left.coeff 123 =
      (((456205404628667992814031 * 10 ^ 70 +
        1165003356843074834218572157262706082128078959866613161614337494639072) * 10 ^ 70 +
        6848284824160671486764611363975991894283979344146934368753501125443054) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 124 = 21 +
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
  rw [recurrence2Scalar4Left_coeff_123_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_124_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (124 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (124 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_124 :
    recurrence2Scalar4Left.coeff 124 =
      -(((2780431439932103405501538 * 10 ^ 70 +
        6208457735823345730322394106165801839044283760083953048604145512419757) * 10 ^ 70 +
        4231218063131354716992211231972757765943274043551036059403326652548886) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 125 = 22 +
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
  rw [recurrence2Scalar4Left_coeff_124_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_125_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (125 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (125 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_125 :
    recurrence2Scalar4Left.coeff 125 =
      (((8010844829303995634855589 * 10 ^ 70 +
        2949027590342968920824904577092088497739402704125099131315385800129617) * 10 ^ 70 +
        0781626213554226554796399854106644601705214571493461810956259214843047) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 126 = 23 +
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
  rw [recurrence2Scalar4Left_coeff_125_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_126_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (126 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (126 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_126 :
    recurrence2Scalar4Left.coeff 126 =
      -(((7468484638975642947458692 * 10 ^ 70 +
        1804523080192372898742964994294110192912854593864771992120952169815455) * 10 ^ 70 +
        0591987641702225937734906787651277661789810786462982996934661821587506) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 127 = 24 +
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
  rw [recurrence2Scalar4Left_coeff_126_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_127_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (127 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (127 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_127 :
    recurrence2Scalar4Left.coeff 127 =
      -(((17331021611144372787976777 * 10 ^ 70 +
        2640662742797661888345838114271211597507138673305063790086774132825886) * 10 ^ 70 +
        2244762687954472202299065758576694778237230431612153698785106300610174) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 128 = 25 +
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
  rw [recurrence2Scalar4Left_coeff_127_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_128_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (128 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (128 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_128 :
    recurrence2Scalar4Left.coeff 128 =
      -(((49844373502006962935882162 * 10 ^ 70 +
        8536729192547874228632201826388620195402570874535415247719494376216841) * 10 ^ 70 +
        7040296643185445364379579805974401825067200046573345964919357589165002) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 129 = 26 +
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
  rw [recurrence2Scalar4Left_coeff_128_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_129_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (129 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (129 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_129 :
    recurrence2Scalar4Left.coeff 129 =
      (((546104713969803732079355812 * 10 ^ 70 +
        9846742740315633063247415535867903410737799376486953530620673558152794) * 10 ^ 70 +
        4919048028573828501361511558485652474691578112714459983628049676695156) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 130 = 27 +
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
  rw [recurrence2Scalar4Left_coeff_129_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_130_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (130 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (130 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_130 :
    recurrence2Scalar4Left.coeff 130 =
      (((2692610385420627680577425526 * 10 ^ 70 +
        0153473078604382837583857892007691797008059289569223464427984574018974) * 10 ^ 70 +
        1557376573085903274948103959140494811670582227128022816793985823391175) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 131 = 28 +
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
  rw [recurrence2Scalar4Left_coeff_130_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_131_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (131 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (131 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_131 :
    recurrence2Scalar4Left.coeff 131 =
      -(((44522646370733572211456720171 * 10 ^ 70 +
        6140061308906167932464704539527628950767811291665185237593039889945830) * 10 ^ 70 +
        8382193646000926143832907225004877217352605181661986779733031097689613) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 132 = 29 +
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
  rw [recurrence2Scalar4Left_coeff_131_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_132_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (132 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (132 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_132 :
    recurrence2Scalar4Left.coeff 132 =
      (((209573661799076231107067166247 * 10 ^ 70 +
        5428720492622010952516914315442846694068023516850571752068051596848417) * 10 ^ 70 +
        1858535874280981098516093596565530301705948873120836902824699835016558) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 133 = 30 +
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
  rw [recurrence2Scalar4Left_coeff_132_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_133_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (133 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (133 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_133 :
    recurrence2Scalar4Left.coeff 133 =
      -(((188106800644912474402774914160 * 10 ^ 70 +
        8931160225072001652808771881959790869311679204908190388221562619690813) * 10 ^ 70 +
        5280170623077060976953635045321587106993433895766034342175705598787038) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 134 = 31 +
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
  rw [recurrence2Scalar4Left_coeff_133_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_134_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (134 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (134 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_134 :
    recurrence2Scalar4Left.coeff 134 =
      -(((3049262546120484070176474186921 * 10 ^ 70 +
        9879008807093498228483599844127161136009551230903497513905535987955149) * 10 ^ 70 +
        6743620220775346808868401815365889072092038929041193895479569861950569) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 135 = 32 +
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
  rw [recurrence2Scalar4Left_coeff_134_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_135_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (135 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (135 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_135 :
    recurrence2Scalar4Left.coeff 135 =
      (((17548813072879125081958983939050 * 10 ^ 70 +
        5940574347720143437302335878221969231401797260548608492905417707917202) * 10 ^ 70 +
        3272204603185933982235867319740517742245793139008081861417973846886111) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 136 = 33 +
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
  rw [recurrence2Scalar4Left_coeff_135_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_136_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (136 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (136 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_136 :
    recurrence2Scalar4Left.coeff 136 =
      -(((28902554736574572213488030882563 * 10 ^ 70 +
        6595479266250287982052893012396958856265632008809398721864116930378336) * 10 ^ 70 +
        2786753605437075416378152622909637759206509238122045124508799304280286) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 137 = 34 +
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
  rw [recurrence2Scalar4Left_coeff_136_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_137_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (137 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (137 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_137 :
    recurrence2Scalar4Left.coeff 137 =
      -(((137991320345582148214155534347927 * 10 ^ 70 +
        6281364241808863210039485850309031905778408861429523271916300358355700) * 10 ^ 70 +
        2588489695575993029509928527639022312822562684981900842702897981601721) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 138 = 35 +
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
  rw [recurrence2Scalar4Left_coeff_137_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_138_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (138 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (138 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_138 :
    recurrence2Scalar4Left.coeff 138 =
      (((922408292309697517846165857549460 * 10 ^ 70 +
        7924628473497421478457351171375155258593373720458725261068336169518434) * 10 ^ 70 +
        2302971459795882973156235413739626018485939210947845862045128144481805) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 139 = 36 +
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
  rw [recurrence2Scalar4Left_coeff_138_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_139_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (139 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (139 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_139 :
    recurrence2Scalar4Left.coeff 139 =
      -(((1441469331387171781223281928413725 * 10 ^ 70 +
        8456462162563712240215281862508377328052849692812039573363673889118451) * 10 ^ 70 +
        1904809237834288301344929705679899165641862699171067210365544395746824) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 140 = 37 +
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
  rw [recurrence2Scalar4Left_coeff_139_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_140_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (140 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (140 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_140 :
    recurrence2Scalar4Left.coeff 140 =
      -(((7348773007351291141367865724461546 * 10 ^ 70 +
        5967696701980965985853959616943055080304591535712360114073577607132047) * 10 ^ 70 +
        3070768636007825991831235745897217541763362426012535095655093589387121) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 141 = 38 +
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
  rw [recurrence2Scalar4Left_coeff_140_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_141_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (141 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (141 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_141 :
    recurrence2Scalar4Left.coeff 141 =
      (((43886235980854821754821154885988881 * 10 ^ 70 +
        3161588410774097564634156194046218065021168621761663292310760216586904) * 10 ^ 70 +
        0040693833354824169555193406470037593046316059988821867876909628079161) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 142 = 39 +
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
  rw [recurrence2Scalar4Left_coeff_141_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_142_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (142 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (142 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_142 :
    recurrence2Scalar4Left.coeff 142 =
      -(((47961917039214965160427338289058468 * 10 ^ 70 +
        3919506867417923249372834421185725870011745276751426384591043437053549) * 10 ^ 70 +
        9044668638176510951608491298570365101328577510081821414782836631196114) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 143 = 40 +
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
  rw [recurrence2Scalar4Left_coeff_142_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_143_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (143 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (143 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_143 :
    recurrence2Scalar4Left.coeff 143 =
      -(((423186580490919511151734353116647072 * 10 ^ 70 +
        7976305021074112228700125692126543207048395746945503942387848032197882) * 10 ^ 70 +
        8871300997941545039852296753376411360037347978539294967661439142682609) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 144 = 41 +
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
  rw [recurrence2Scalar4Left_coeff_143_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_144_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (144 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (144 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_144 :
    recurrence2Scalar4Left.coeff 144 =
      (((2023155248354868351355587285156572075 * 10 ^ 70 +
        4884372143122318941832521086375589632769905475830640389169226549293436) * 10 ^ 70 +
        9366945050052385132298820151286886873138789480843014047685297703518228) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 145 = 42 +
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
  rw [recurrence2Scalar4Left_coeff_144_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_145 :
    recurrence2Scalar4Left.coeff 145 =
      -(((1134086474517799524630003660133573024 * 10 ^ 70 +
        0791645750594411997848101336559458368327371848122928291336711731391272) * 10 ^ 70 +
        0751278205749629430337096856800404969663187786337026695493262805021966) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 43 +
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
  rw [recurrence2Scalar4Left_coeff_145_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_146 :
    recurrence2Scalar4Left.coeff 146 =
      -(((22110752005525530241212165658307786385 * 10 ^ 70 +
        1848163292687920337356111786523282469584540284747178390647900874023788) * 10 ^ 70 +
        7860181527433204922056698109351730427405287644130629263175065844072903) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 44 +
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
  rw [recurrence2Scalar4Left_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_147 :
    recurrence2Scalar4Left.coeff 147 =
      (((84086394949574660032975700606475689665 * 10 ^ 70 +
        7376895011745317975646298871030439380676923418186338736350170648870930) * 10 ^ 70 +
        6168772018030592902963427207615639518683213324978974565854652238997496) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 45 +
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
  rw [recurrence2Scalar4Left_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_148 :
    recurrence2Scalar4Left.coeff 148 =
      (((19030239086501714855346587319795399690 * 10 ^ 70 +
        0089251001301894383493119235165142783285452574844560003136073906707868) * 10 ^ 70 +
        0845941435744947391025980858002013463696455990014391815612846114724038) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 46 +
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
  rw [recurrence2Scalar4Left_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_149 :
    recurrence2Scalar4Left.coeff 149 =
      -(((1152646211265298055523698385065082399747 * 10 ^ 70 +
        5675792620965682501920294636130788633156816199044135035028902958349361) * 10 ^ 70 +
        5248316321436094543030351493870614944150882891908213936281585470942768) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 47 +
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
  rw [recurrence2Scalar4Left_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_150 :
    recurrence2Scalar4Left.coeff 150 =
      (((3488809287594225980100346116583649755388 * 10 ^ 70 +
        5362042784332438194052717636204380765654376431347046199908763362551906) * 10 ^ 70 +
        1291836465334437341633893201403415321021553747437385487293612764498704) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 151 = 48 +
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
  rw [recurrence2Scalar4Left_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_151 :
    recurrence2Scalar4Left.coeff 151 =
      (((3691120595969250517862542997146589302571 * 10 ^ 70 +
        2821173629571587207249960563444493652133377684865377088440015321980150) * 10 ^ 70 +
        8088840705398153244977220619392960113578448971325063436395978330582962) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 152 = 49 +
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
  rw [recurrence2Scalar4Left_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_152 :
    recurrence2Scalar4Left.coeff 152 =
      -(((59356012823588566275641733107201565038180 * 10 ^ 70 +
        9531209901176503255301905046465229424569308204877310986105593665873935) * 10 ^ 70 +
        1111051712037449483764197423959800059200245566532740558297728497964933) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 153 = 50 +
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
  rw [recurrence2Scalar4Left_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_153 :
    recurrence2Scalar4Left.coeff 153 =
      (((162205208915403929653617191810771875037183 * 10 ^ 70 +
        6503525016215698603743652654428883045135716460080680349239756488592115) * 10 ^ 70 +
        0170085243040418535249029985068427904831360662149131920465323171604082) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 51 +
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
  rw [recurrence2Scalar4Left_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_154 :
    recurrence2Scalar4Left.coeff 154 =
      (((184484120363571790395532168863970735187704 * 10 ^ 70 +
        9113678719400519422922495873190272559979817115220823368993016563273086) * 10 ^ 70 +
        9362515525109531578678965313749295946580072882436146967771536626761257) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 52 +
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
  rw [recurrence2Scalar4Left_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_155 :
    recurrence2Scalar4Left.coeff 155 =
      -(((2750637285253598605453399906689973701197065 * 10 ^ 70 +
        1837974658454399255386477863519728837914161952172645210650475587508568) * 10 ^ 70 +
        2792664146065191024454584588207824814173499337295300121832396697716531) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 53 +
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
  rw [recurrence2Scalar4Left_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_156 :
    recurrence2Scalar4Left.coeff 156 =
      (((7937907304371841097827554388151839247667749 * 10 ^ 70 +
        2966591634437003083557539860245941298278181314644225461446333962313536) * 10 ^ 70 +
        1280155989915309489772028385300320551490502649466260473331861889258512) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 54 +
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
  rw [recurrence2Scalar4Left_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_157 :
    recurrence2Scalar4Left.coeff 157 =
      (((3716394600907540583604121411683579062354679 * 10 ^ 70 +
        5472222306048290346240776200283877202475943906239200461633566904911019) * 10 ^ 70 +
        1052686496773699869041851118250476628873059477377435615744387583064336) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 55 +
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
  rw [recurrence2Scalar4Left_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_158 :
    recurrence2Scalar4Left.coeff 158 =
      -(((107909514947551584099607675338699703792978165 * 10 ^ 70 +
        5033570539982971392803600894332614938642346398734415228860332123187237) * 10 ^ 70 +
        1733717116062920093634991920876412039519162277646385002534564873676681) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 56 +
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
  rw [recurrence2Scalar4Left_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_159 :
    recurrence2Scalar4Left.coeff 159 =
      (((362046759673773106128143270428309188097888746 * 10 ^ 70 +
        8384240027524053392507395988975833349617888679988026623028260472919572) * 10 ^ 70 +
        6223238741879188236173422507695046951475954918957695373081916892389173) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 57 +
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
  rw [recurrence2Scalar4Left_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_160 :
    recurrence2Scalar4Left.coeff 160 =
      -(((143744135169124506820509696818796067723042129 * 10 ^ 70 +
        7350686398735372726440324168179295916058365304748149592131166057320834) * 10 ^ 70 +
        4747711864899158015680085832012198407275598682158514900712913702940528) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 58 +
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
  rw [recurrence2Scalar4Left_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_161 :
    recurrence2Scalar4Left.coeff 161 =
      -(((3430935731897317067368722610176726410787984558 * 10 ^ 70 +
        3598648487153604254816243012411012183563791637857005401317038372203093) * 10 ^ 70 +
        8846825433422899224974766935011877261862812690709478931181778547388882) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 59 +
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
  rw [recurrence2Scalar4Left_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_162 :
    recurrence2Scalar4Left.coeff 162 =
      (((14314145447881452826295458900853761996954786714 * 10 ^ 70 +
        6155936712724919412498353802876699351157740760829283443065474538334901) * 10 ^ 70 +
        4672639511936085733169872327323540774658269992016623651790690838572719) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 60 +
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
  rw [recurrence2Scalar4Left_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_163 :
    recurrence2Scalar4Left.coeff 163 =
      -(((17215159279104187118593767092012485116660633363 * 10 ^ 70 +
        6429083218019836491905769919692890815980392040849039030398207763757776) * 10 ^ 70 +
        9629694160808283358764288843260914767421370155213280449775162188555549) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 61 +
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
  rw [recurrence2Scalar4Left_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_164 :
    recurrence2Scalar4Left.coeff 164 =
      -(((82985856118093275622980456589221000788652426847 * 10 ^ 70 +
        5242298366313574022589415382981853220029974165427914712462309743424629) * 10 ^ 70 +
        0489659050096070214790978411791104285036471901241365253648286076989138) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 62 +
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
  rw [recurrence2Scalar4Left_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_165 :
    recurrence2Scalar4Left.coeff 165 =
      (((478973487238661385658073099470157747211623594479 * 10 ^ 70 +
        0158611186654498514673304504645520394563965511663878179232466262169324) * 10 ^ 70 +
        6784193925707764666556795638950534004669252526876047258848218223893879) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 63 +
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
  rw [recurrence2Scalar4Left_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_166 :
    recurrence2Scalar4Left.coeff 166 =
      -(((943846181480528333816212225137081644254918324047 * 10 ^ 70 +
        1096832959011199483204311579837364271051978722077372123571709397696165) * 10 ^ 70 +
        7330325602601859336714123533273684058399688071512166315108290635079919) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 64 +
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
  rw [recurrence2Scalar4Left_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_167 :
    recurrence2Scalar4Left.coeff 167 =
      -(((1177263971484134200742054739801034695455967752827 * 10 ^ 70 +
        1079812441308948497361728021802906523513996678458036208148040542780263) * 10 ^ 70 +
        3523503974653972417267125397923126606496049164616281907247389165038009) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 65 +
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
  rw [recurrence2Scalar4Left_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_168 :
    recurrence2Scalar4Left.coeff 168 =
      (((13338385552444384851869141872638977088674115703057 * 10 ^ 70 +
        0163023392348896429906455106916096463250914293045152057239132747252295) * 10 ^ 70 +
        2551672661082386114203206021715392563065907693127390045761985131977953) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 66 +
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
  rw [recurrence2Scalar4Left_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_169 :
    recurrence2Scalar4Left.coeff 169 =
      -(((37979896281591786772564534680682588304940843096671 * 10 ^ 70 +
        9948199555082672235704218444749361455784669819275718860499934733773170) * 10 ^ 70 +
        1176243502617786154809950024319158919107091259084768553540165368053019) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 67 +
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
  rw [recurrence2Scalar4Left_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_170 :
    recurrence2Scalar4Left.coeff 170 =
      (((16263695733934571592531681281430319925735165392871 * 10 ^ 70 +
        4321787044914537598204363813522557419896463812499629095744499175263399) * 10 ^ 70 +
        5115176822724786324134945257336060987593143445968496913817436071529407) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 68 +
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
  rw [recurrence2Scalar4Left_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_171 :
    recurrence2Scalar4Left.coeff 171 =
      (((286944791261925270779768795125868463070235714779998 * 10 ^ 70 +
        6109577591419549744201803592768889996401150534935306070225885812025831) * 10 ^ 70 +
        6651305979154359954263137942637450977226820140511849008980999439209663) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 69 +
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
  rw [recurrence2Scalar4Left_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_172 :
    recurrence2Scalar4Left.coeff 172 =
      -(((1208862559061915942560483517415666402254076955894127 * 10 ^ 70 +
        2022606332133481180823780748351958219267015277249387418401044771947644) * 10 ^ 70 +
        4376583745198986899471248078253452081109311200634954973810984020734947) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 70 +
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
  rw [recurrence2Scalar4Left_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_173 :
    recurrence2Scalar4Left.coeff 173 =
      (((1944649495381908230751871555470610628689982373686726 * 10 ^ 70 +
        2311815590192251769053786790570029315890800683166041814350560100608291) * 10 ^ 70 +
        8628569647439590186811314863482528879088910523112751664866587153304222) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 71 +
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
  rw [recurrence2Scalar4Left_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_174 :
    recurrence2Scalar4Left.coeff 174 =
      (((3310043034431278706132791349508831970130291970377013 * 10 ^ 70 +
        3784312701604503486396895183005522266789538435656311609519367104650450) * 10 ^ 70 +
        2279669670603707463436379976324633042642623024086923573005431124279432) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 72 +
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
  rw [recurrence2Scalar4Left_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_175 :
    recurrence2Scalar4Left.coeff 175 =
      -(((29061050217685026169877826640027394948860171141597404 * 10 ^ 70 +
        7277660562960406941743413635955631688392335628862656522672681486832388) * 10 ^ 70 +
        2127343978106603247628682619067864606451602924025835890297432385277675) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 73 +
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
  rw [recurrence2Scalar4Left_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_176 :
    recurrence2Scalar4Left.coeff 176 =
      (((80825932310029386705821028756098804614795735037079068 * 10 ^ 70 +
        4085109126660501332869830315525943721125271612726280554321638432475411) * 10 ^ 70 +
        3021652844204206490032054976489382734493840688875591958910255211603098) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 74 +
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
  rw [recurrence2Scalar4Left_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_177 :
    recurrence2Scalar4Left.coeff 177 =
      -(((61970203960130356132636825075908766614562126517586612 * 10 ^ 70 +
        4876554090696777156001916193836856149248949267382987813406093841068468) * 10 ^ 70 +
        4482815863403884914568746737446165959388232385865736227674537947815581) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 75 +
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
  rw [recurrence2Scalar4Left_coeff_177_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_178 :
    recurrence2Scalar4Left.coeff 178 =
      -(((426087980785212255659370950123505758694131086019762168 * 10 ^ 70 +
        6684490784841802762298083783306112889597781633274850221029535925591314) * 10 ^ 70 +
        7415414294079044882849891806252066165271151665992027294453487206054109) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 76 +
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
  rw [recurrence2Scalar4Left_coeff_178_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_179 :
    recurrence2Scalar4Left.coeff 179 =
      (((2098395723081014029648560913694401880597755219555454633 * 10 ^ 70 +
        6055684643016852534480475299517296517559097131702814217458639220629342) * 10 ^ 70 +
        8695655559960289536625130173431011498896002241059128918111888579755700) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 77 +
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
  rw [recurrence2Scalar4Left_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_180 :
    recurrence2Scalar4Left.coeff 180 =
      -(((4548310284950352531535502164462727678752003103018853255 * 10 ^ 70 +
        8910352023674990250774479966830806257240171688222449793989232974886566) * 10 ^ 70 +
        2894028945952269975696267998066321314447263964873669689682607294730213) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 78 +
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
  rw [recurrence2Scalar4Left_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_181 :
    recurrence2Scalar4Left.coeff 181 =
      (((930650417028740722153572982980585055506137209729230118 * 10 ^ 70 +
        9941868031456872276531526909954051170662821157423594792351393160202450) * 10 ^ 70 +
        9805627973980275765636957004668318501493169790655660030125051308581598) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 79 +
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
  rw [recurrence2Scalar4Left_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_182 :
    recurrence2Scalar4Left.coeff 182 =
      (((30985261269171846391695202295104082774271385064874635563 * 10 ^ 70 +
        6593695642197639137334378812284003164320300457882700590438043821519630) * 10 ^ 70 +
        8470215367710283775064876798475571257300135570571940031442938149520675) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 80 +
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
  rw [recurrence2Scalar4Left_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_183 :
    recurrence2Scalar4Left.coeff 183 =
      -(((123819398060667256963134803376031425418983013355495633838 * 10 ^ 70 +
        2368927255270219720139657370663425099710489451490048545627709334438177) * 10 ^ 70 +
        5858707677040474769943149758830197859640607974994746229614190136786971) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 81 +
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
  rw [recurrence2Scalar4Left_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_184 :
    recurrence2Scalar4Left.coeff 184 =
      (((240675603875707876309311350996783298829195105055060281530 * 10 ^ 70 +
        2221521732625550731739786859486467723487335352708003341356401305042033) * 10 ^ 70 +
        1219322979791680560319581526628695072615651550819343993209444122649605) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 82 +
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
  rw [recurrence2Scalar4Left_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_185 :
    recurrence2Scalar4Left.coeff 185 =
      -(((19061527746200405627412436892680053291234266644377944787 * 10 ^ 70 +
        1757302780837601444609218649191323100561269200624478351501461013420924) * 10 ^ 70 +
        9936066401481808488360429887187074968710222987563222542464987081514290) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 83 +
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
  rw [recurrence2Scalar4Left_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_186 :
    recurrence2Scalar4Left.coeff 186 =
      -(((1627949653795240896780413946324346024267677451767303134362 * 10 ^ 70 +
        6867899552367409861361753578075949626558465261379816776406216754369130) * 10 ^ 70 +
        6067820910532590076265812217548960141867041971584617866442303458041725) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 84 +
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
  rw [recurrence2Scalar4Left_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_187 :
    recurrence2Scalar4Left.coeff 187 =
      (((6292961356627434509191394352328122248879102484847680490162 * 10 ^ 70 +
        8391520191215601107930284871779376381258774169938628312729110147540905) * 10 ^ 70 +
        0472027636526566725001395257951983322977340652577741062169367600163335) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 85 +
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
  rw [recurrence2Scalar4Left_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_188 :
    recurrence2Scalar4Left.coeff 188 =
      -(((12737413072199246568362288327373829875473921017278671811089 * 10 ^ 70 +
        5927521499314886615997639867026075091712544228205333657157141673322248) * 10 ^ 70 +
        7059594012720475647315619073182514215179154180520039232535240833146700) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 86 +
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
  rw [recurrence2Scalar4Left_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_189 :
    recurrence2Scalar4Left.coeff 189 =
      (((6150400160683154879244788430936716715913437785859932217530 * 10 ^ 70 +
        0691399162937367579449708498498616827277885417212676500541089739327358) * 10 ^ 70 +
        5903813484348313539861493672716680350088335014868905902295815709419721) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 87 +
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
  rw [recurrence2Scalar4Left_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_190 :
    recurrence2Scalar4Left.coeff 190 =
      (((60400456361386790598115046214903924857698536403202056631579 * 10 ^ 70 +
        0553651759886491720191055186280433870065707069136990571323717055220509) * 10 ^ 70 +
        8659670572115036062298701909797814410610794154757505616961879247618732) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 88 +
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
  rw [recurrence2Scalar4Left_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_191 :
    recurrence2Scalar4Left.coeff 191 =
      -(((268887622811659333922900090327245913205802587360255712682504 * 10 ^ 70 +
        9565661521707272596751430855293272022242615539569839505578619533268975) * 10 ^ 70 +
        3071330581394990306860561340756128592231401139195077418648212799302753) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 89 +
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
  rw [recurrence2Scalar4Left_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_192 :
    recurrence2Scalar4Left.coeff 192 =
      (((638151811013234694063500608344322681909701326619022484961303 * 10 ^ 70 +
        8255057276995276115268923028042843677811811373728551661703951714417166) * 10 ^ 70 +
        9216368847428038543609112559857063095484662537659267826238903071791273) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 90 +
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
  rw [recurrence2Scalar4Left_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_193 :
    recurrence2Scalar4Left.coeff 193 =
      -(((751684925467382539006493709922707406625265442856593831231938 * 10 ^ 70 +
        1449248626434919630507856722267071993431223924653385214761378940496170) * 10 ^ 70 +
        4765797389855031567164394778285745497845510638136511432142533191897272) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 91 +
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
  rw [recurrence2Scalar4Left_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_194 :
    recurrence2Scalar4Left.coeff 194 =
      -(((1038115777529604779242251427543453599382025758222428473940534 * 10 ^ 70 +
        4973874502574353608276635764923602600733739405578949694165701309513444) * 10 ^ 70 +
        4987622099922667144254895874173107293451119032494427157820775842749155) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 92 +
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
  rw [recurrence2Scalar4Left_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_195 :
    recurrence2Scalar4Left.coeff 195 =
      (((8443887623079004840029131435630820013103222378023201779487619 * 10 ^ 70 +
        5762294424129767746414014760603926120434541466806260138674330171059617) * 10 ^ 70 +
        3565194960570321121179111075986847669478072377156977642155136056997215) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 93 +
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
  rw [recurrence2Scalar4Left_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_196 :
    recurrence2Scalar4Left.coeff 196 =
      -(((25988380427028819830633862667310875719043427288033394575370826 * 10 ^ 70 +
        9685245093543784633398840273511263798168370068613950072529510290380622) * 10 ^ 70 +
        9722743705326687489717882596249909768470179345845987753727302669158709) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 94 +
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
  rw [recurrence2Scalar4Left_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_197 :
    recurrence2Scalar4Left.coeff 197 =
      (((50120410365496759174737178587938783371739294315307910484474137 * 10 ^ 70 +
        7921971865724403739099089585513532599488726151912382994847924235338340) * 10 ^ 70 +
        3518615033951596009170940584444621339142067760634271267240539751649265) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 95 +
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
  rw [recurrence2Scalar4Left_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_198 :
    recurrence2Scalar4Left.coeff 198 =
      -(((43684506964067896684957258574145584736576696789049882956427146 * 10 ^ 70 +
        3992602409085591699053583129865659082426198172967609589290382216290893) * 10 ^ 70 +
        9192671346150517452069829707574556065617841845488617850467774291290929) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 96 +
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
  rw [recurrence2Scalar4Left_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_199 :
    recurrence2Scalar4Left.coeff 199 =
      -(((111409589393948041439415601560068170112749289571538326674130176 * 10 ^ 70 +
        1751727744088141837091814301144521595205249383066583046614163604458389) * 10 ^ 70 +
        3101945848854921965896139577497599062941269200264997927492137663828496) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 97 +
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
  rw [recurrence2Scalar4Left_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_200 :
    recurrence2Scalar4Left.coeff 200 =
      (((659612386200120735749869537972392868348565572281491942391916621 * 10 ^ 70 +
        2402303964772000771662841512866002872443634405977956053405045322123992) * 10 ^ 70 +
        0476071201437236939459533443723136053015700490773397151762827883190975) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 98 +
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
  rw [recurrence2Scalar4Left_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_201 :
    recurrence2Scalar4Left.coeff 201 =
      -(((1910145307895521764819552292682799261015739705955689194520515688 * 10 ^ 70 +
        4845900321952777290776216401094129427331751264846832857008270486375936) * 10 ^ 70 +
        1232548623837476025828675394838449299943727702603655056472929422798221) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 99 +
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
  rw [recurrence2Scalar4Left_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_202 :
    recurrence2Scalar4Left.coeff 202 =
      (((3809524652486926977562369306850281123483893852241945576653934166 * 10 ^ 70 +
        6985568294667077488090698990272456018744247599075068549786791252206246) * 10 ^ 70 +
        6461831076623353251570806171189090343626820791166159536842604181797442) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 100 +
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
  rw [recurrence2Scalar4Left_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_203 :
    recurrence2Scalar4Left.coeff 203 =
      -(((4704016638078736998155297826290059619575724111695539213319682616 * 10 ^ 70 +
        5030850184972157636919595164425636706747403945549809751027371978551269) * 10 ^ 70 +
        3406222281159951552914397433046762030283808630752765862564592605125874) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 101 +
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
  rw [recurrence2Scalar4Left_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_204 :
    recurrence2Scalar4Left.coeff 204 =
      -(((1167329874637797918873686780140892517276992991755257735570223139 * 10 ^ 70 +
        6940291293971809408186940523100455457691297468276256693169298966491223) * 10 ^ 70 +
        8976589261309341052616733504021054409553876047794425277180478463483285) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 102 +
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
  rw [recurrence2Scalar4Left_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_205 :
    recurrence2Scalar4Left.coeff 205 =
      (((27263074207577445220628455763624123254573888202809170669035743145 * 10 ^ 70 +
        6215010080025674550986732973572858084238263294935238412552052676974740) * 10 ^ 70 +
        5399616848254408081187272691571128496715692241693256922782685036416469) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 103 +
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
  rw [recurrence2Scalar4Left_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_206 :
    recurrence2Scalar4Left.coeff 206 =
      -(((97074888138047149311087106525008127876983835372209504184491063783 * 10 ^ 70 +
        9713696898894706944523258122515619224535297868795782998708404233749002) * 10 ^ 70 +
        5043808304190074119166629115462745596368194311106812148809806888740135) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 104 +
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
  rw [recurrence2Scalar4Left_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_207 :
    recurrence2Scalar4Left.coeff 207 =
      (((238180666293798216379793215204988567408287338816341768757848151835 * 10 ^ 70 +
        0063433704337396204883098139141416506196423969718056551421413047304249) * 10 ^ 70 +
        3235734193251770370010405416996139924516685677514216971525713216204640) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 105 +
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
  rw [recurrence2Scalar4Left_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_208 :
    recurrence2Scalar4Left.coeff 208 =
      -(((453196897081291254153890968261201679044494920137217481805156960206 * 10 ^ 70 +
        3212353386255983109538877773078492975735422685744637450381509988485298) * 10 ^ 70 +
        4387800845354111602406633283394308264899781537870594905827409238427410) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 106 +
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
  rw [recurrence2Scalar4Left_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_209 :
    recurrence2Scalar4Left.coeff 209 =
      (((643095837466498307689750552176476460581123110459096357719200113093 * 10 ^ 70 +
        2193304332561714776388391922210207553718680226473628278484913268056789) * 10 ^ 70 +
        0302933323861031867346009019531267455298711501920915848069891408237069) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 107 +
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
  rw [recurrence2Scalar4Left_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_210 :
    recurrence2Scalar4Left.coeff 210 =
      -(((451340811990318091730283453625367904017693280950100923862023603392 * 10 ^ 70 +
        1826994727577542840847687159828079945750674262362614311815716755237747) * 10 ^ 70 +
        6747027732336250991768465244005639284230611578001038394978383627410580) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 108 +
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
  rw [recurrence2Scalar4Left_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_211 :
    recurrence2Scalar4Left.coeff 211 =
      -(((997602887395623159397345571280407311459864676169060815281575402124 * 10 ^ 70 +
        7900809597936422712893194307598667525417242497709647672718110275271423) * 10 ^ 70 +
        4511369368018090698754471340873901773077514038233277766770170944335934) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 109 +
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
  rw [recurrence2Scalar4Left_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_212 :
    recurrence2Scalar4Left.coeff 212 =
      (((5460983507174505190151637732476064444772760346033114156869829219984 * 10 ^ 70 +
        3591234974384925592510221336171742877564123967716574466934839206659873) * 10 ^ 70 +
        6555370815672050933669157487836839544991545088935880175155635109857539) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 110 +
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
  rw [recurrence2Scalar4Left_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_213 :
    recurrence2Scalar4Left.coeff 213 =
      -(((15967202558881762006757163384480717609785698115482298821985246771854 * 10 ^ 70 +
        3815636617971187155461953292269115105157183432344364389201352972092085) * 10 ^ 70 +
        5858779982167323070147931936744020139692736308939803762383760739213394) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 111 +
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
  rw [recurrence2Scalar4Left_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_214 :
    recurrence2Scalar4Left.coeff 214 =
      (((37043709159462220990011842767114419211251786307369564913722737650769 * 10 ^ 70 +
        7758927784285450501775927941127909254851203163083382063951868192886761) * 10 ^ 70 +
        4166760793071846252312373793296739367370985942922608993075018436445285) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 112 +
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
  rw [recurrence2Scalar4Left_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_215 :
    recurrence2Scalar4Left.coeff 215 =
      -(((74454770881176143976920082833656379190871956677181597753049721220264 * 10 ^ 70 +
        8180096362198972782195216800102509854101112681107440102687887926371321) * 10 ^ 70 +
        1490256461290775641869658259448866161660942369102476653287109561506316) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 113 +
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
  rw [recurrence2Scalar4Left_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_216 :
    recurrence2Scalar4Left.coeff 216 =
      (((134003060405536959135041502986243314434557516211893740461040589395667 * 10 ^ 70 +
        7866945185112468189635281138803216935926518616521702836311734134633934) * 10 ^ 70 +
        8063756043304869939076072967285043933565614321949619597886958809715249) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 114 +
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
  rw [recurrence2Scalar4Left_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_217 :
    recurrence2Scalar4Left.coeff 217 =
      -(((218936614815821699987241046515332615570958883828919973888737212564108 * 10 ^ 70 +
        6727847785060523425128642831179537547154466856868854259301632743576645) * 10 ^ 70 +
        7549253433671536305832697628148821156588274940677886785438099429233441) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 115 +
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
  rw [recurrence2Scalar4Left_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_218 :
    recurrence2Scalar4Left.coeff 218 =
      (((325692413521851710894100240192710303890355938398332160505435814071260 * 10 ^ 70 +
        8546685252372202791339290378361664335734916394597231618242475999713279) * 10 ^ 70 +
        5413116657022418162005455968990480612827375444165059103317042511766706) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 116 +
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
  rw [recurrence2Scalar4Left_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_219 :
    recurrence2Scalar4Left.coeff 219 =
      -(((438170456375454917485448699281360494608807468392503279132383101937280 * 10 ^ 70 +
        6510481184815264902995955835612954218553403231444518610429974663767059) * 10 ^ 70 +
        9097003297655567478817490867590257177520044757232723464387232829755821) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 117 +
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
  rw [recurrence2Scalar4Left_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_220 :
    recurrence2Scalar4Left.coeff 220 =
      (((521456696753516695916316001438152283784366721488765527445369265076622 * 10 ^ 70 +
        3104483169934605770707035036281393491999837590966495642461288188125727) * 10 ^ 70 +
        9924072035367436600122987548330879364060117739665513647467123547863560) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 118 +
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
  rw [recurrence2Scalar4Left_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_221 :
    recurrence2Scalar4Left.coeff 221 =
      -(((516756994163840112989163722876100210896925505458855604462059042323261 * 10 ^ 70 +
        0911595919175642724501451042181172485947202102145137315318558570738727) * 10 ^ 70 +
        9019855232116965595980798996939723889698773939575952480104034956417081) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 119 +
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
  rw [recurrence2Scalar4Left_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_222 :
    recurrence2Scalar4Left.coeff 222 =
      (((339981883412546331721515556785593324168305048781341135414924776908170 * 10 ^ 70 +
        9256187609209932256357098314468929606713301910714231266768143705124883) * 10 ^ 70 +
        3783541080672104281324822729475593873237055996740425608572961035241525) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 120 +
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
  rw [recurrence2Scalar4Left_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_223 :
    recurrence2Scalar4Left.coeff 223 =
      (((113440904869323901937885627177393995452428635229239082208175126464062 * 10 ^ 70 +
        0328761999895422438878712696311228423582183708872829843738812020910196) * 10 ^ 70 +
        7854255987385433753571964052100231824465416086870777281324116376921751) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 121 +
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
  rw [recurrence2Scalar4Left_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_224 :
    recurrence2Scalar4Left.coeff 224 =
      -(((955689033537035643495952829496818140248169529440544132427459569967921 * 10 ^ 70 +
        2232297509110277705097561910962287091321138829434741157535952987102522) * 10 ^ 70 +
        9945783684767560525685170664124794357865996553985283605877314046667966) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 122 +
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
  rw [recurrence2Scalar4Left_coeff_224_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_225 :
    recurrence2Scalar4Left.coeff 225 =
      (((2285511510727141944925958653422759309929110460161509861454221922149434 * 10 ^ 70 +
        2973013941837576807105492794024864945113268164024618501618106394640263) * 10 ^ 70 +
        7990945886818060778149237804014520687992881712719622337925169329406851) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 123 +
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
  rw [recurrence2Scalar4Left_coeff_225_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_226 :
    recurrence2Scalar4Left.coeff 226 =
      -(((4161470413785962910862444100619517673731881193380224085430887985060997 * 10 ^ 70 +
        7900039896641714685761745587999396863816848853006924797804817905361794) * 10 ^ 70 +
        2785515688300530017268623948392686902589127050962885912704891230782340) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 124 +
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
  rw [recurrence2Scalar4Left_coeff_226_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_227 :
    recurrence2Scalar4Left.coeff 227 =
      (((6574567033371985923845909658358650569444596878429785874021824003933861 * 10 ^ 70 +
        4032053844094867653991891770797135897734168085493404532354587979874062) * 10 ^ 70 +
        3562004449594393104481778942489252378480790094086372184986696937154702) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 125 +
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
  rw [recurrence2Scalar4Left_coeff_227_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_228 :
    recurrence2Scalar4Left.coeff 228 =
      -(((9427281533582818841310743815196606075441756441672285137795044080997707 * 10 ^ 70 +
        6340906766835153635050689047310905850483226132948691382860618069632054) * 10 ^ 70 +
        4765342652578071566495332352068620831113820958262542852856273951240780) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 126 +
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
  rw [recurrence2Scalar4Left_coeff_228_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_229 :
    recurrence2Scalar4Left.coeff 229 =
      ((((1 * 10 ^ 70 +
        2526311942217179231118363549469978453513074824085221272394103531818704) * 10 ^ 70 +
        9736362614292532185493497145094313805285234503357113403301940159839007) * 10 ^ 70 +
        0075513106104941764465181174216864161238847592617903026729784473314583) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 127 +
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
  rw [recurrence2Scalar4Left_coeff_229_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
