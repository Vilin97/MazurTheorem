/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B4_coeff_0
  recurrence2B4_coeff_1
  recurrence2B4_coeff_2
  recurrence2B4_coeff_3
  recurrence2B4_coeff_4
  recurrence2B4_coeff_5
  recurrence2B4_coeff_6
  recurrence2B4_coeff_7
  recurrence2B4_coeff_8
  recurrence2B4_coeff_9
  recurrence2B4_coeff_10
  recurrence2B4_coeff_11
  recurrence2B4_coeff_12
  recurrence2B4_coeff_13
  recurrence2B4_coeff_14
  recurrence2B4_coeff_15
  recurrence2B4_coeff_16
  recurrence2B4_coeff_17
  recurrence2B4_coeff_18
  recurrence2B4_coeff_19
  recurrence2B4_coeff_20
  recurrence2B4_coeff_21
  recurrence2B4_coeff_22
  recurrence2B4_coeff_23
  recurrence2B4_coeff_24
  recurrence2B4_coeff_25
  recurrence2B4_coeff_26
  recurrence2B4_coeff_27
  recurrence2B4_coeff_28
  recurrence2B4_coeff_29
  recurrence2B4_coeff_30
  recurrence2B4_coeff_31
  recurrence2B4_coeff_32
  recurrence2B4_coeff_33
  recurrence2B4_coeff_34
  recurrence2B4_coeff_35
  recurrence2B4_coeff_36
  recurrence2B4_coeff_37
  recurrence2B4_coeff_38
  recurrence2B4_coeff_39
  recurrence2B4_coeff_40
  recurrence2B4_coeff_41
  recurrence2B4_coeff_42
  recurrence2B4_coeff_43
  recurrence2B4_coeff_44
  recurrence2B4_coeff_45
  recurrence2B4_coeff_46
  recurrence2B4_coeff_47
  recurrence2B4_coeff_48
  recurrence2B4_coeff_49
  recurrence2B4_coeff_50
  recurrence2B4_coeff_51
  recurrence2B4_coeff_52
  recurrence2B4_coeff_53
  recurrence2B4_coeff_54
  recurrence2B4_coeff_55
  recurrence2B4_coeff_56
  recurrence2B4_coeff_57
  recurrence2B4_coeff_58
  recurrence2B4_coeff_59
  recurrence2B4_coeff_60
  recurrence2B4_coeff_61
  recurrence2B4_coeff_62
  recurrence2B4_coeff_63
  recurrence2B4_coeff_64
  recurrence2B4_coeff_65
  recurrence2B4_coeff_66
  recurrence2B4_coeff_67
  recurrence2B4_coeff_68
  recurrence2B4_coeff_69
  recurrence2B4_coeff_70
  recurrence2B4_coeff_71
  recurrence2B4_coeff_72
  recurrence2B4_coeff_73
  recurrence2B4_coeff_74
  recurrence2B4_coeff_75
  recurrence2B4_coeff_76
  recurrence2B4_coeff_77
  recurrence2B4_coeff_78
  recurrence2B4_coeff_79
  recurrence2B4_coeff_80
  recurrence2B4_coeff_81
  recurrence2B4_coeff_82
  recurrence2B4_coeff_83
  recurrence2B4_coeff_84
  recurrence2B4_coeff_85
  recurrence2B4_coeff_86
  recurrence2B4_coeff_87
  recurrence2B4_coeff_88
  recurrence2B4_coeff_89
  recurrence2B4_coeff_90
  recurrence2B4_coeff_91
  recurrence2B4_coeff_92
  recurrence2B4_coeff_93
  recurrence2B4_coeff_94
  recurrence2B4_coeff_95
  recurrence2B4_coeff_96
  recurrence2B4_coeff_97
  recurrence2B4_coeff_98
  recurrence2B4_coeff_99
  recurrence2B4_coeff_100
  recurrence2B4_coeff_101
  recurrence2B4_coeff_102
  recurrence2B4_coeff_103
  recurrence2B4_coeff_104
  recurrence2B4_coeff_105
  recurrence2B4_coeff_106
  recurrence2B4_coeff_107
  recurrence2B4_coeff_108
  recurrence2B4_coeff_109
  recurrence2B4_coeff_110
  recurrence2B4_coeff_111
  recurrence2B4_coeff_112
  recurrence2B4_coeff_113
  recurrence2B4_coeff_114
  recurrence2B4_coeff_115
  recurrence2B4_coeff_116
  recurrence2B4_coeff_117
  recurrence2B4_coeff_118
  recurrence2B4_coeff_119
  recurrence2B4_coeff_120
  recurrence2B4_coeff_121
  recurrence2B4_coeff_122
  recurrence2B4_coeff_123
  recurrence2B4_coeff_124
  recurrence2B4_coeff_125
  recurrence2B4_coeff_126
  recurrence2B4_coeff_127
  recurrence2B4_coeff_128
  recurrence2B4_coeff_129
  recurrence2B4_coeff_130
  recurrence2B4_coeff_131
  recurrence2B4_coeff_132
  recurrence2B4_coeff_133
  recurrence2B4_coeff_134
  recurrence2B4_coeff_135
  recurrence2B4_coeff_136
  recurrence2B4_coeff_137
  recurrence2B4_coeff_138
  recurrence2QuotientConstant_coeff_0
  recurrence2QuotientConstant_coeff_1
  recurrence2QuotientConstant_coeff_2
  recurrence2QuotientConstant_coeff_3
  recurrence2QuotientConstant_coeff_4
  recurrence2QuotientConstant_coeff_5
  recurrence2QuotientConstant_coeff_6
  recurrence2QuotientConstant_coeff_7
  recurrence2QuotientConstant_coeff_8
  recurrence2QuotientConstant_coeff_9
  recurrence2QuotientConstant_coeff_10
  recurrence2QuotientConstant_coeff_11
  recurrence2QuotientConstant_coeff_12
  recurrence2QuotientConstant_coeff_13
  recurrence2QuotientConstant_coeff_14
  recurrence2QuotientConstant_coeff_15
  recurrence2QuotientConstant_coeff_16
  recurrence2QuotientConstant_coeff_17
  recurrence2QuotientConstant_coeff_18
  recurrence2QuotientConstant_coeff_19
  recurrence2QuotientConstant_coeff_20
  recurrence2QuotientConstant_coeff_21
  recurrence2QuotientConstant_coeff_22
  recurrence2QuotientConstant_coeff_23
  recurrence2QuotientConstant_coeff_24
  recurrence2QuotientConstant_coeff_25
  recurrence2QuotientConstant_coeff_26
  recurrence2QuotientConstant_coeff_27
  recurrence2QuotientConstant_coeff_28
  recurrence2QuotientConstant_coeff_29
  recurrence2QuotientConstant_coeff_30
  recurrence2QuotientConstant_coeff_31
  recurrence2QuotientConstant_coeff_32
  recurrence2QuotientConstant_coeff_33
  recurrence2QuotientConstant_coeff_34
  recurrence2QuotientConstant_coeff_35
  recurrence2QuotientConstant_coeff_36
  recurrence2QuotientConstant_coeff_37
  recurrence2QuotientConstant_coeff_38
  recurrence2QuotientConstant_coeff_39
  recurrence2QuotientConstant_coeff_40
  recurrence2QuotientConstant_coeff_41
  recurrence2QuotientConstant_coeff_42
  recurrence2QuotientConstant_coeff_43
  recurrence2QuotientConstant_coeff_44
  recurrence2QuotientConstant_coeff_45
  recurrence2QuotientConstant_coeff_46
  recurrence2QuotientConstant_coeff_47
  recurrence2QuotientConstant_coeff_48
  recurrence2QuotientConstant_coeff_49
  recurrence2QuotientConstant_coeff_50
  recurrence2QuotientConstant_coeff_51
  recurrence2QuotientConstant_coeff_52
  recurrence2QuotientConstant_coeff_53
  recurrence2QuotientConstant_coeff_54
  recurrence2QuotientConstant_coeff_55
  recurrence2QuotientConstant_coeff_56
  recurrence2QuotientConstant_coeff_57
  recurrence2QuotientConstant_coeff_58
  recurrence2QuotientConstant_coeff_59
  recurrence2QuotientConstant_coeff_60
  recurrence2QuotientConstant_coeff_61
  recurrence2QuotientConstant_coeff_62
  recurrence2QuotientConstant_coeff_63
  recurrence2QuotientConstant_coeff_64
  recurrence2QuotientConstant_coeff_65
  recurrence2QuotientConstant_coeff_66
  recurrence2QuotientConstant_coeff_67
  recurrence2QuotientConstant_coeff_68
  recurrence2QuotientConstant_coeff_69
  recurrence2QuotientConstant_coeff_70
  recurrence2QuotientConstant_coeff_71
  recurrence2QuotientConstant_coeff_72
  recurrence2QuotientConstant_coeff_73
  recurrence2QuotientConstant_coeff_74
  recurrence2QuotientConstant_coeff_75
  recurrence2QuotientConstant_coeff_76
  recurrence2QuotientConstant_coeff_77
  recurrence2QuotientConstant_coeff_78
  recurrence2QuotientConstant_coeff_79
  recurrence2QuotientConstant_coeff_80
  recurrence2QuotientConstant_coeff_81
  recurrence2QuotientConstant_coeff_82
  recurrence2QuotientConstant_coeff_83
  recurrence2QuotientConstant_coeff_84
  recurrence2QuotientConstant_coeff_85
  recurrence2QuotientConstant_coeff_86
  recurrence2QuotientConstant_coeff_87
  recurrence2QuotientConstant_coeff_88
  recurrence2QuotientConstant_coeff_89
  recurrence2QuotientConstant_coeff_90
  recurrence2QuotientConstant_coeff_91
  recurrence2QuotientConstant_coeff_92
  recurrence2QuotientConstant_coeff_93
  recurrence2QuotientConstant_coeff_94
  recurrence2QuotientConstant_coeff_95
  recurrence2QuotientConstant_coeff_96
  recurrence2QuotientConstant_coeff_97
  recurrence2QuotientConstant_coeff_98
  recurrence2QuotientConstant_coeff_99
  recurrence2QuotientConstant_coeff_100
  recurrence2QuotientConstant_coeff_101
  recurrence2QuotientConstant_coeff_102
  recurrence2QuotientConstant_coeff_103
  recurrence2QuotientConstant_coeff_104
  recurrence2QuotientConstant_coeff_105
  recurrence2QuotientConstant_coeff_106
  recurrence2QuotientConstant_coeff_107
  recurrence2QuotientConstant_coeff_108
  recurrence2QuotientConstant_coeff_109
  recurrence2QuotientConstant_coeff_110
  recurrence2QuotientConstant_coeff_111
  recurrence2QuotientConstant_coeff_112
  recurrence2QuotientConstant_coeff_113
  recurrence2QuotientConstant_coeff_114
  recurrence2QuotientConstant_coeff_115
  recurrence2QuotientConstant_coeff_116
  recurrence2QuotientConstant_coeff_117
  recurrence2QuotientConstant_coeff_118
  recurrence2QuotientConstant_coeff_119
  recurrence2QuotientConstant_coeff_120
  recurrence2QuotientConstant_coeff_121
  recurrence2QuotientConstant_coeff_122
  recurrence2QuotientConstant_coeff_123
  recurrence2QuotientConstant_coeff_124
  recurrence2QuotientConstant_coeff_125
  recurrence2QuotientConstant_coeff_126
  recurrence2QuotientConstant_coeff_127
  recurrence2QuotientConstant_coeff_128
  recurrence2QuotientConstant_coeff_129
  recurrence2QuotientConstant_coeff_130
  recurrence2QuotientConstant_coeff_131
  recurrence2QuotientConstant_coeff_132
  recurrence2QuotientConstant_coeff_133
  recurrence2QuotientConstant_coeff_134
  recurrence2QuotientConstant_coeff_135
  recurrence2QuotientConstant_coeff_136
  recurrence2QuotientConstant_coeff_137
  recurrence2QuotientConstant_coeff_138
  recurrence2QuotientConstant_coeff_139
  recurrence2QuotientConstant_coeff_140
  recurrence2QuotientConstant_coeff_141
  recurrence2QuotientConstant_coeff_142
  recurrence2QuotientConstant_coeff_143
  recurrence2QuotientConstant_coeff_144
  recurrence2QuotientConstant_coeff_145
  recurrence2QuotientConstant_coeff_146
  recurrence2QuotientConstant_coeff_147
  recurrence2QuotientConstant_coeff_148
  recurrence2QuotientConstant_coeff_149
  recurrence2QuotientConstant_coeff_150
  recurrence2QuotientConstant_coeff_151
  recurrence2QuotientConstant_coeff_152
  recurrence2QuotientConstant_coeff_153
  recurrence2QuotientConstant_coeff_154
  recurrence2QuotientConstant_coeff_155
  recurrence2QuotientConstant_coeff_156
  recurrence2QuotientConstant_coeff_157
  recurrence2QuotientConstant_coeff_158
  recurrence2QuotientConstant_coeff_159
  recurrence2QuotientConstant_coeff_160
  recurrence2QuotientConstant_coeff_161
  recurrence2QuotientConstant_coeff_162
  recurrence2QuotientConstant_coeff_163
  recurrence2QuotientConstant_coeff_164
  recurrence2QuotientConstant_coeff_165
  recurrence2QuotientConstant_coeff_166
  recurrence2QuotientConstant_coeff_167
  recurrence2QuotientConstant_coeff_168
  recurrence2QuotientConstant_coeff_169
  recurrence2QuotientConstant_coeff_170
  recurrence2QuotientConstant_coeff_171
  recurrence2QuotientConstant_coeff_172
  recurrence2QuotientConstant_coeff_173
  recurrence2QuotientConstant_coeff_174
  recurrence2QuotientConstant_coeff_175
  recurrence2QuotientConstant_coeff_176
  recurrence2QuotientConstant_coeff_177
  recurrence2QuotientConstant_coeff_178
  recurrence2QuotientConstant_coeff_179
  recurrence2QuotientConstant_coeff_180
  recurrence2QuotientConstant_coeff_181
  recurrence2QuotientConstant_coeff_182
  recurrence2QuotientConstant_coeff_183
  recurrence2QuotientConstant_coeff_184
  recurrence2QuotientConstant_coeff_185
  recurrence2QuotientConstant_coeff_186
  recurrence2QuotientConstant_coeff_187
  recurrence2QuotientConstant_coeff_188
  recurrence2QuotientConstant_coeff_189
  recurrence2QuotientConstant_coeff_190
  recurrence2QuotientConstant_coeff_191
  recurrence2QuotientConstant_coeff_192
  recurrence2QuotientConstant_coeff_193
  recurrence2QuotientConstant_coeff_194
  recurrence2QuotientConstant_coeff_195
  recurrence2QuotientConstant_coeff_196
  recurrence2QuotientConstant_coeff_197
  recurrence2QuotientConstant_coeff_198
  recurrence2QuotientConstant_coeff_199
  recurrence2QuotientConstant_coeff_200
  recurrence2QuotientConstant_coeff_201
  recurrence2QuotientConstant_coeff_202
  recurrence2QuotientConstant_coeff_203
  recurrence2QuotientConstant_coeff_204
  recurrence2QuotientConstant_coeff_205
  recurrence2QuotientConstant_coeff_206
  recurrence2QuotientConstant_coeff_207
  recurrence2QuotientConstant_coeff_208
  recurrence2QuotientConstant_coeff_209
  recurrence2QuotientConstant_coeff_210
  recurrence2QuotientConstant_coeff_211
  recurrence2QuotientConstant_coeff_212
  recurrence2QuotientConstant_coeff_213
  recurrence2QuotientConstant_coeff_214
  recurrence2QuotientConstant_coeff_215
  recurrence2QuotientConstant_coeff_216
  recurrence2QuotientConstant_coeff_217
  recurrence2QuotientConstant_coeff_218
  recurrence2QuotientConstant_coeff_219
  recurrence2QuotientConstant_coeff_220
  recurrence2QuotientConstant_coeff_221
  recurrence2QuotientConstant_coeff_222
  recurrence2QuotientConstant_coeff_223
  recurrence2QuotientConstant_coeff_224
  recurrence2QuotientConstant_coeff_225
  recurrence2QuotientConstant_coeff_226
  recurrence2QuotientConstant_coeff_227
  recurrence2QuotientConstant_coeff_228
  recurrence2QuotientConstant_coeff_229
  recurrence2QuotientConstant_coeff_230
  recurrence2QuotientConstant_coeff_231
  recurrence2QuotientConstant_coeff_232
  recurrence2QuotientConstant_coeff_233

theorem recurrence2Scalar4Main_coeff_0 :
    recurrence2Scalar4Main.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_1 :
    recurrence2Scalar4Main.coeff 1 =
      (249856 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_2 :
    recurrence2Scalar4Main.coeff 2 =
      (-40673349504 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_3 :
    recurrence2Scalar4Main.coeff 3 =
      (-31692865560192 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_4 :
    recurrence2Scalar4Main.coeff 4 =
      (3291188531349761664 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_5 :
    recurrence2Scalar4Main.coeff 5 =
      (-3480881830719843630816 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_6 :
    recurrence2Scalar4Main.coeff 6 =
      (8303077905757658041697488 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_7 :
    recurrence2Scalar4Main.coeff 7 =
      (-5952960795618782891138446896 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_8 :
    recurrence2Scalar4Main.coeff 8 =
      (4239039691545034413938343067968 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_9 :
    recurrence2Scalar4Main.coeff 9 =
      (-1108999817610760276456728189772116 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_10 :
    recurrence2Scalar4Main.coeff 10 =
      (-879404444846688240049478462286453460 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_11 :
    recurrence2Scalar4Main.coeff 11 =
      (939611237573654044146889270247206768276 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_12 :
    recurrence2Scalar4Main.coeff 12 =
      (-507425420430130957343437123433596229259872 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_13 :
    recurrence2Scalar4Main.coeff 13 =
      (182743277310660316413857185512364905932920342 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_14 :
    recurrence2Scalar4Main.coeff 14 =
      (-48975048467151843684296548364815862064873115261 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_15 :
    recurrence2Scalar4Main.coeff 15 =
      (10062807556420562450589963722305949594006953059135 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_16 :
    recurrence2Scalar4Main.coeff 16 =
      (-1614044628969205897038223873657750544476127786925824 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_17 :
    recurrence2Scalar4Main.coeff 17 =
      (204093929148467027448200174553914448554237594985292056 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_18 :
    recurrence2Scalar4Main.coeff 18 =
      (-20353418814107303099029103807745798884839481581506009273 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_19 :
    recurrence2Scalar4Main.coeff 19 =
      (1581348607168643735193590308757357878381380952998329628657 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_20 :
    recurrence2Scalar4Main.coeff 20 =
      (-91613463484000408122859167471709724971594235209925399509704 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_21 :
    recurrence2Scalar4Main.coeff 21 =
      (3362895072337246421970539926197033299072690334540022718846116 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_22 :
    recurrence2Scalar4Main.coeff 22 =
      (3236177908509504561074664452017666418996221846508700695131225 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_23 :
    recurrence2Scalar4Main.coeff 23 =
      (-12073189214839841896399852282392545181426566136101219112282944976 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_24 :
    recurrence2Scalar4Main.coeff 24 =
      (1133950865713386967368814247800034955197110951269964651327242189721 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_25 :
    recurrence2Scalar4Main.coeff 25 =
      (-67046835957481374794204915342108721999972616382079831077304003191512 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_26 :
    recurrence2Scalar4Main.coeff 26 =
      (2631456392340516607937015199329241194956040528172990436207381288263100 : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_27 :
    recurrence2Scalar4Main.coeff 27 =
      -((3 * 10 ^ 70 +
        6081947441045949917891851730056392974796481933781132703585175242658638) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_28 :
    recurrence2Scalar4Main.coeff 28 =
      -((434 * 10 ^ 70 +
        8228445539279716202190039865932775439611063680157929426149341345168506) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_29 :
    recurrence2Scalar4Main.coeff 29 =
      ((47263 * 10 ^ 70 +
        4159529257082267868672721380591614973748609201160717539567418188853958) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_30 :
    recurrence2Scalar4Main.coeff 30 =
      -((2897142 * 10 ^ 70 +
        4069604605716771596449321477038994243256351672674033283278551834625921) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_31 :
    recurrence2Scalar4Main.coeff 31 =
      ((128804979 * 10 ^ 70 +
        3159381907641390317279288579144892950706200645209176939250952303350199) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_32 :
    recurrence2Scalar4Main.coeff 32 =
      -((4090080286 * 10 ^ 70 +
        2452713159666853904214766548469147457897883873454883355230895876828134) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_33 :
    recurrence2Scalar4Main.coeff 33 =
      ((60236757903 * 10 ^ 70 +
        2277114294693727580410149091589464853653074017801610408636472201861460) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_34 :
    recurrence2Scalar4Main.coeff 34 =
      ((3075251495715 * 10 ^ 70 +
        8204603919086240991036050915070225930120782084941969539552392966674416) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_35 :
    recurrence2Scalar4Main.coeff 35 =
      -((322652558811675 * 10 ^ 70 +
        3836026331147777066624765173618566120298215015846947301817771947434301) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_36 :
    recurrence2Scalar4Main.coeff 36 =
      ((17196519308938885 * 10 ^ 70 +
        5763480630064009021145425151018818547100870150286408297370015708360155) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_37 :
    recurrence2Scalar4Main.coeff 37 =
      -((663084583324531001 * 10 ^ 70 +
        6928382168052673279817221168622425829031390167727105468226207772565903) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_38 :
    recurrence2Scalar4Main.coeff 38 =
      ((19571265022454862880 * 10 ^ 70 +
        9994159090442480873384296876967267201357869067338608689707836326763837) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_39 :
    recurrence2Scalar4Main.coeff 39 =
      -((434402180760613279469 * 10 ^ 70 +
        0447230961482820764939717652703064534399034696396545887521000128238789) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_40 :
    recurrence2Scalar4Main.coeff 40 =
      ((6483126182535593169574 * 10 ^ 70 +
        8029123225484672588699599760829269788616587525694574717047997533060481) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_41 :
    recurrence2Scalar4Main.coeff 41 =
      -((31650637528139668185442 * 10 ^ 70 +
        7102387951478644976794048226507172964736953689429997668724177611091365) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_42 :
    recurrence2Scalar4Main.coeff 42 =
      -((1317241765267522884683902 * 10 ^ 70 +
        8534898847333782491743209246126736218203953480748384209399925355802158) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_43 :
    recurrence2Scalar4Main.coeff 43 =
      ((37196497490964372819954239 * 10 ^ 70 +
        9621626226854229031693894436248793545263852606127338841102790767394403) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_44 :
    recurrence2Scalar4Main.coeff 44 =
      -((191631976988440352304910640 * 10 ^ 70 +
        8059721362994064989930891576639587249834825960591770091535440990222095) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_45 :
    recurrence2Scalar4Main.coeff 45 =
      -((14017755055104280889294085241 * 10 ^ 70 +
        3224353303888201995953837807537825295293693934777013891668139516777745) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_46 :
    recurrence2Scalar4Main.coeff 46 =
      ((441559353242691785442136801407 * 10 ^ 70 +
        4513908551761020564737504546556870823243662574357395242802996177862847) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_47 :
    recurrence2Scalar4Main.coeff 47 =
      -((3185999894931051309344435075307 * 10 ^ 70 +
        8714614356131859603163059674033137837247556564838366942780497948315332) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_48 :
    recurrence2Scalar4Main.coeff 48 =
      -((215536373114938785338375196636209 * 10 ^ 70 +
        8297364102940351897328227265258851293871100686239408152464828703470228) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_49 :
    recurrence2Scalar4Main.coeff 49 =
      ((10952506632125987856817621130607884 * 10 ^ 70 +
        4149718188343869932910140650428397959533145128252240994446536784300105) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_50 :
    recurrence2Scalar4Main.coeff 50 =
      -((317917730501661704176150114287425366 * 10 ^ 70 +
        5326856347341669947693751841104978866540221730883982305359559374918632) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_51 :
    recurrence2Scalar4Main.coeff 51 =
      ((7005456112974587241384012109193096120 * 10 ^ 70 +
        7358578698788570048052194289528846739138196036054345063193393140421185) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_52 :
    recurrence2Scalar4Main.coeff 52 =
      -((126851765244169990384380893340945365174 * 10 ^ 70 +
        6096689713337402501651328548024120043962138845420608044311483637821710) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_53 :
    recurrence2Scalar4Main.coeff 53 =
      ((1937709118074667890715593937499706881479 * 10 ^ 70 +
        9620599064184356377266084991088851337120522117455543845080582542709072) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_54 :
    recurrence2Scalar4Main.coeff 54 =
      -((24623929391431641338611045835260054188912 * 10 ^ 70 +
        8164323636681492473548597685800033959646535997336208496010148127420283) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_55 :
    recurrence2Scalar4Main.coeff 55 =
      ((234446314243960867728896408926262150033341 * 10 ^ 70 +
        3989732927621179774087386254759192221363146369553891854125527588462539) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_56 :
    recurrence2Scalar4Main.coeff 56 =
      -((727108551778550120984680002452101350044293 * 10 ^ 70 +
        8507375771051627221467495164843639889354142234574977195853295255587428) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_57 :
    recurrence2Scalar4Main.coeff 57 =
      -((36456429221933729350567761045044494322057394 * 10 ^ 70 +
        5202198478266821386328803196310881194251420065583190618232177175452901) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_58 :
    recurrence2Scalar4Main.coeff 58 =
      ((1223925292547623501750649970459019548170361188 * 10 ^ 70 +
        8777728203047542219120982669986039055382867205016162054043828655920814) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_59 :
    recurrence2Scalar4Main.coeff 59 =
      -((26162815009729504066136575674876129015101947089 * 10 ^ 70 +
        4843658303545582553159591004051320073724954114662762173541161757615091) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_60 :
    recurrence2Scalar4Main.coeff 60 =
      ((452786705577841346236822838666822620884452185142 * 10 ^ 70 +
        3544714683355292602201881240913480576269417186330568700541624152987359) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_61 :
    recurrence2Scalar4Main.coeff 61 =
      -((6733666220336704824639590936406250599459485235030 * 10 ^ 70 +
        3226218194094742112590482936429464472561496609857086330943044464414836) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_62 :
    recurrence2Scalar4Main.coeff 62 =
      ((87650955310926674250591896726281942534591525939647 * 10 ^ 70 +
        7349708317745592096408558268794252764534720136929010300901443194981151) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_63 :
    recurrence2Scalar4Main.coeff 63 =
      -((996907028333650168796638736647200215531259192573477 * 10 ^ 70 +
        9839548413154013551974678819397701211850175090000090260516654861788227) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_64 :
    recurrence2Scalar4Main.coeff 64 =
      ((9654606362158582774465279309070927478386515804500069 * 10 ^ 70 +
        7943961096181468113316149164461790404957582558571205559596677952532468) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_65 :
    recurrence2Scalar4Main.coeff 65 =
      -((72825580349139250446053180550500455440680759324662956 * 10 ^ 70 +
        9310087330568291941127114051284597575330014418436504312250665102449490) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_66 :
    recurrence2Scalar4Main.coeff 66 =
      ((263802642964431761674668970327998799313594710435981244 * 10 ^ 70 +
        2081279003682151457708412127948336688205111968909928476121103986158357) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_67 :
    recurrence2Scalar4Main.coeff 67 =
      ((4065052847498050757509705752733266047845901890764243241 * 10 ^ 70 +
        5334776588735574854601167764800584065911961743320753308126592742219004) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_68 :
    recurrence2Scalar4Main.coeff 68 =
      -((121768510833189567120376917953968156625107382182232112695 * 10 ^ 70 +
        6417276591343342043176254544810405154183838420875729489129948094709862) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_69 :
    recurrence2Scalar4Main.coeff 69 =
      ((2071105166327971700256300716635169499070171589398739692074 * 10 ^ 70 +
        2702763705904534643340542362363991594247293435991000190238804049024569) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_70 :
    recurrence2Scalar4Main.coeff 70 =
      -((28536363578583557116654752787894420189161011528685256207161 * 10 ^ 70 +
        6944984519673493505648486649338357319655553877839790464682507330595439) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_71 :
    recurrence2Scalar4Main.coeff 71 =
      ((346167489162428908870570693257398419718577939526276127229287 * 10 ^ 70 +
        3189369097329253787619617731549149611693142554514221592536008919045109) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_72 :
    recurrence2Scalar4Main.coeff 72 =
      -((3823266614824763301269698923365357628920246321488647930594371 * 10 ^ 70 +
        0318053377206044947855834348157130041673314001234180840575205811656594) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_73 :
    recurrence2Scalar4Main.coeff 73 =
      ((39115109276825238708146228251463183583386273000382381583588517 * 10 ^ 70 +
        8694652233946433786547349253204357488025355307260375341107714894647928) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_74 :
    recurrence2Scalar4Main.coeff 74 =
      -((374552198524176249013465015478124844500208540778643147694788954 * 10 ^ 70 +
        0379608640647238845808678063856799595093507097861900623967140183098523) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_75 :
    recurrence2Scalar4Main.coeff 75 =
      ((3380017570118113054698705114444925891064855305695418141412919067 * 10 ^ 70 +
        1842366703768101632284679341306572984330801916497137629389419603270367) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_76 :
    recurrence2Scalar4Main.coeff 76 =
      -((28884495551723703889849846768855156030105913285051379720098725791 * 10 ^ 70 +
        6045767787689506691405514391545618010475351366760532737634982735531105) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_77 :
    recurrence2Scalar4Main.coeff 77 =
      ((234570519555910204472982081345532100762381662515172806558616194446 * 10 ^ 70 +
        6553758305200577870289342763962758826923486358348597391416914686441359) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_78 :
    recurrence2Scalar4Main.coeff 78 =
      -((1814934973080970050504009075785489512709820119131772123670703264425 * 10 ^ 70 +
        1395939284270716765267622493028102445935541889803435631559519048413305) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_79 :
    recurrence2Scalar4Main.coeff 79 =
      ((13404555373588168527926642033946613254431870144164614257963460668154 * 10 ^ 70 +
        3515823900173651438263693014172686207544454707950765135769312147430851) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_80 :
    recurrence2Scalar4Main.coeff 80 =
      -((94639624845464271214266950520258821693959212281925361030371106890289 * 10 ^ 70 +
        6085746141846167396595791673448035272364402068303747636330222064319137) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_81 :
    recurrence2Scalar4Main.coeff 81 =
      ((639473917762548384974541323727361877869588767514173082467900560784960 * 10 ^ 70 +
        8557330450143419721853864334705797375612829232394786450591424072769084) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_82 :
    recurrence2Scalar4Main.coeff 82 =
      -((4139286124390950655737272846401902128052583611812816664488007173014253 * 10 ^ 70 +
        0995262462156889442807256761560461149716916022804286413707981962983447) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_83 :
    recurrence2Scalar4Main.coeff 83 =
      (((2 * 10 ^ 70 +
        5688958623154166703514619426854955764319010861582829470483606219367822) * 10 ^ 70 +
        1945308598582825404579579739928430977112857855187935374687213078173234) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_84 :
    recurrence2Scalar4Main.coeff 84 =
      -(((15 * 10 ^ 70 +
        2961379717130581003620433140809714885798062003086966891253778488399675) * 10 ^ 70 +
        7640352757159351034778587094335153542937213238411904904356805494714006) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_85 :
    recurrence2Scalar4Main.coeff 85 =
      (((87 * 10 ^ 70 +
        4228283458439234023731365722513584585126469893515110004003271827953378) * 10 ^ 70 +
        3215259585473116127739922393831734862184828755521409839478497003232446) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_86 :
    recurrence2Scalar4Main.coeff 86 =
      -(((479 * 10 ^ 70 +
        6590440366610652147042962282103064143011155515043962457899160652842453) * 10 ^ 70 +
        4455226841541514872807707840832555759705954970108349788536147944166210) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_87 :
    recurrence2Scalar4Main.coeff 87 =
      (((2525 * 10 ^ 70 +
        8658111264268051598399235535749638603713536592161243422197969531033317) * 10 ^ 70 +
        2195886391504153322881171560006594725642089370943220560237272599305092) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_88 :
    recurrence2Scalar4Main.coeff 88 =
      -(((12759 * 10 ^ 70 +
        3282205886969645508097734383966185912030844640882306903838497069242171) * 10 ^ 70 +
        1550850119707813458697299454642059565425951947749099350669446451654163) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_89 :
    recurrence2Scalar4Main.coeff 89 =
      (((61782 * 10 ^ 70 +
        2426650271630625565318008889360594826812732729203317700877237189642741) * 10 ^ 70 +
        5346563152903707861222318501971684964961555094933673215039702747133180) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_90 :
    recurrence2Scalar4Main.coeff 90 =
      -(((286513 * 10 ^ 70 +
        7970291019839863854815495474156533433743721717484986334017533143350492) * 10 ^ 70 +
        3463487591854299172453879144253473725370884070559868296978703616501400) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_91 :
    recurrence2Scalar4Main.coeff 91 =
      (((1271268 * 10 ^ 70 +
        3718929608219034112632952200725768803857337787167444222884577663182383) * 10 ^ 70 +
        5508237398944266902971106770811567916678764274429857509373601206814292) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_92 :
    recurrence2Scalar4Main.coeff 92 =
      -(((5389006 * 10 ^ 70 +
        1206691789751893371121117702095722304404405330217470161350303461472073) * 10 ^ 70 +
        8611451752313659556319946213334747953464122562834966530941411957264616) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_93 :
    recurrence2Scalar4Main.coeff 93 =
      (((21768707 * 10 ^ 70 +
        3319074545199998278159547420393718899397524107018466904304876181862893) * 10 ^ 70 +
        9280989625243598833558731022792402069461434112500567156717768434745159) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_94 :
    recurrence2Scalar4Main.coeff 94 =
      -(((83382444 * 10 ^ 70 +
        5959815267285047446514402712707818577596217519987682139886964849127082) * 10 ^ 70 +
        9256542801484499372253469655203325752044855825920263531505773808733139) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_95 :
    recurrence2Scalar4Main.coeff 95 =
      (((300152328 * 10 ^ 70 +
        7545854215164530109099935498435159703961031858523524151222160673769097) * 10 ^ 70 +
        8449385248204582011862059116901447254428135962098081065773984007316407) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_96 :
    recurrence2Scalar4Main.coeff 96 =
      -(((999565066 * 10 ^ 70 +
        5636689672446403442235935114865064479464766247480092296276893544482191) * 10 ^ 70 +
        5064483300463019009087610318030581766227490718532132009945527788996405) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_97 :
    recurrence2Scalar4Main.coeff 97 =
      (((2994292985 * 10 ^ 70 +
        7420368695605630342947730362971417449894199381225256534829338326018932) * 10 ^ 70 +
        9138554892476508025734034901844715779848842724029078082864216123642034) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_98 :
    recurrence2Scalar4Main.coeff 98 =
      -(((7616782853 * 10 ^ 70 +
        1324682919024471394514026798163264520171691212068957593842912649503247) * 10 ^ 70 +
        7120329655092148566112583383669775803594722571732084874147213079635431) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_99 :
    recurrence2Scalar4Main.coeff 99 =
      (((13864244084 * 10 ^ 70 +
        3414544898711660718966720424158451466301112407159388900516511740979551) * 10 ^ 70 +
        3299301651664043093233919637883812488796212146451796218667085626568786) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_100 :
    recurrence2Scalar4Main.coeff 100 =
      -(((288436409 * 10 ^ 70 +
        1197628878745525360723139995965786774838962512321627683329417121451230) * 10 ^ 70 +
        8004945292895343234799487628456177814510296843518124033892485072371112) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_101 :
    recurrence2Scalar4Main.coeff 101 =
      -(((158782108135 * 10 ^ 70 +
        6843492514281556817414437578929244787184001207716254837787375965366682) * 10 ^ 70 +
        1947973546742751931929422246874357589612579545223192336997921641160624) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_102 :
    recurrence2Scalar4Main.coeff 102 =
      (((1054932420754 * 10 ^ 70 +
        5112206938546669142744024993404491884992134638541715010290487611829001) * 10 ^ 70 +
        2846488379277951886063533880734568560776011187198079948126756589812274) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_103 :
    recurrence2Scalar4Main.coeff 103 =
      -(((5347729779445 * 10 ^ 70 +
        6675886533091737990104471423018041260670867059861973491846004657813170) * 10 ^ 70 +
        9922929808797269631382728901502260385555265817105208347602084955740485) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_104 :
    recurrence2Scalar4Main.coeff 104 =
      (((24817902439485 * 10 ^ 70 +
        4474104157441279445075035609469718907670402435477371272457291861171748) * 10 ^ 70 +
        4549273565857196231838271207246132717354298944052156116044277665293088) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_105 :
    recurrence2Scalar4Main.coeff 105 =
      -(((107842170242512 * 10 ^ 70 +
        4829849379954216152419429367123005672933037421557395871883104193059352) * 10 ^ 70 +
        0134264060821522775843675752166190451454830967428351696990735552102494) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_106 :
    recurrence2Scalar4Main.coeff 106 =
      (((418804949805655 * 10 ^ 70 +
        6767680290884422919665232721027159049084729397746846340274961379717549) * 10 ^ 70 +
        6166155492250374099497942004173334164564020633130402414439043401617493) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_107 :
    recurrence2Scalar4Main.coeff 107 =
      -(((1325115745051766 * 10 ^ 70 +
        8220014587295843998608288506792287876047166552265841543565003608359539) * 10 ^ 70 +
        1858283804831061598942804579251365421948864004552990865303479216902915) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_108 :
    recurrence2Scalar4Main.coeff 108 =
      (((2750729802837968 * 10 ^ 70 +
        7069279671027966841336422899664093774155384902059859330748982307466414) * 10 ^ 70 +
        8208435189851061624277916909998176244473142683379032793403420927441439) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_109 :
    recurrence2Scalar4Main.coeff 109 =
      (((444398811614565 * 10 ^ 70 +
        0784482198118174064718636790912623371389278133515075296824157325890375) * 10 ^ 70 +
        8690020771956037351958718296004596136898095561341633674784556168094448) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_110 :
    recurrence2Scalar4Main.coeff 110 =
      -(((31526462079253535 * 10 ^ 70 +
        0514920276405864768046162972985770751612066121865006040446353477523583) * 10 ^ 70 +
        2811509111911832223940285684928105868949029790783213690820589250854206) : ℚ) := by
  unfold recurrence2Scalar4Main
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

theorem recurrence2Scalar4Main_coeff_111 :
    recurrence2Scalar4Main.coeff 111 =
      (((118818000232643291 * 10 ^ 70 +
        4301773752822373073763523401430552996767141874675196433221937329806187) * 10 ^ 70 +
        6149347158204368056237810460043140057352790960585748700557008233670802) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_112 :
    recurrence2Scalar4Main.coeff 112 =
      (((23926725873534171 * 10 ^ 70 +
        0826098593673462868065893300733793082846399638551985902309446678508440) * 10 ^ 70 +
        7620921296674911915224808712570259097318593497170728412269397132816536) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_113 :
    recurrence2Scalar4Main.coeff 113 =
      -(((2627351438604726611 * 10 ^ 70 +
        4816642319959175853057715704923794167333853580589050970812332701684599) * 10 ^ 70 +
        4060759850476793671151889075819507327015829345120673609165042656249729) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_114 :
    recurrence2Scalar4Main.coeff 114 =
      (((15749583774724378009 * 10 ^ 70 +
        4657778449500366247413096600990116363385816876057885267418414080450314) * 10 ^ 70 +
        8286659808112472083859979189063303829631470405046782369014795160062596) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_115 :
    recurrence2Scalar4Main.coeff 115 =
      -(((47907470629301076862 * 10 ^ 70 +
        4621395706249176498642418876511056594840953396167231916848787628506769) * 10 ^ 70 +
        3497680420475797225328180029211368119080572514704844265409803271009939) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_116 :
    recurrence2Scalar4Main.coeff 116 =
      (((10985859719237421517 * 10 ^ 70 +
        2081622372887559089497362663992927379044347704053252003790974492104029) * 10 ^ 70 +
        9670444114032896015073703264174110551832714683407779251148884404448631) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_117 :
    recurrence2Scalar4Main.coeff 117 =
      (((764433328644672075852 * 10 ^ 70 +
        3805546629986458643107900556030617400972182800177695467551479502853098) * 10 ^ 70 +
        4937660402363741792080416636476958201882475817154937540211138279638661) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_118 :
    recurrence2Scalar4Main.coeff 118 =
      -(((4848000089229824656638 * 10 ^ 70 +
        3125567622411161587059238911950318446986529924091503641365912556605766) * 10 ^ 70 +
        6225141408572524529073765200199690255000799439901247126256744898639918) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_119 :
    recurrence2Scalar4Main.coeff 119 =
      (((17138009860597048446649 * 10 ^ 70 +
        1444638224321382997508691867385310704125380610547384488826470972516554) * 10 ^ 70 +
        5998304656562609148976235012018997161306304607727244091779878236053477) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_120 :
    recurrence2Scalar4Main.coeff 120 =
      -(((28953321128216495479174 * 10 ^ 70 +
        0456169964962126587797895306696883976293549452258338517056445762942974) * 10 ^ 70 +
        2216557297189056211701743329112324199370492714421725140473597488976715) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_121 :
    recurrence2Scalar4Main.coeff 121 =
      -(((75904435843073238333999 * 10 ^ 70 +
        5551042427556993750639900008864670065840597078327175505186070951330124) * 10 ^ 70 +
        0351232463674658548505786548889562215511025522014535237759025115861444) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_122 :
    recurrence2Scalar4Main.coeff 122 =
      (((846477459632349175871613 * 10 ^ 70 +
        6673686422083359515479464147078002656779761299993050213897961839458256) * 10 ^ 70 +
        1643666450156690889335224726117354088347149999077265974508660383917124) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_123 :
    recurrence2Scalar4Main.coeff 123 =
      -(((3991545860204878873519143 * 10 ^ 70 +
        5538339736818257141093107288077772831078988854924878065534023103156300) * 10 ^ 70 +
        8768823299484832676250572869322541059583720412433191203590518205641143) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_124 :
    recurrence2Scalar4Main.coeff 124 =
      (((12650051693847502158391852 * 10 ^ 70 +
        5474802905907651950871871434920248569968246946622819093272751112852223) * 10 ^ 70 +
        5621581218794245873738624003501547333780229573082678144488084687605070) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_125 :
    recurrence2Scalar4Main.coeff 125 =
      -(((21793714389280097669156375 * 10 ^ 70 +
        1617235482438571194995630874240033143052142047847441196876658947861110) * 10 ^ 70 +
        9836949033443828113535986303905285241023208009677052696158462614567490) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_126 :
    recurrence2Scalar4Main.coeff 126 =
      -(((58326897119567058887784137 * 10 ^ 70 +
        6344424321012859970994462055806337082149340363316878828388136034880702) * 10 ^ 70 +
        7612555133331249099943421842621063465100527908759587708663334838624477) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_127 :
    recurrence2Scalar4Main.coeff 127 =
      (((759382780333859236919800007 * 10 ^ 70 +
        2204905426277118825002575265095827091255846577889884952800813084230078) * 10 ^ 70 +
        5069222419747592021800261526963981593865372769812427090742740483151215) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_128 :
    recurrence2Scalar4Main.coeff 128 =
      -(((3914788301951312963679688069 * 10 ^ 70 +
        9438331027772603299789991299717327345161357784305444275386450596207663) * 10 ^ 70 +
        1395235731463356902721885610095247680069668652767436999649058406956171) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_129 :
    recurrence2Scalar4Main.coeff 129 =
      (((11364881669289916241026333923 * 10 ^ 70 +
        7777792084443408633429249544099961682378242729923072754347368465762627) * 10 ^ 70 +
        1301114238285711685412174705429285648467171735075175155469318511794145) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_130 :
    recurrence2Scalar4Main.coeff 130 =
      -(((4203052715916917545803756059 * 10 ^ 70 +
        4158305607901017847429379964487286500555144334721851260313415970352202) * 10 ^ 70 +
        6473113723407645571697740556767204463541623272507772920296650711560660) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_131 :
    recurrence2Scalar4Main.coeff 131 =
      -(((137227176412893863710802281480 * 10 ^ 70 +
        6767729811671224988345240618816200916414086214571061959414105322027218) * 10 ^ 70 +
        4666633557674741812750292902375278199894663507757622797282255677221905) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_132 :
    recurrence2Scalar4Main.coeff 132 =
      (((698474561630178872887612207795 * 10 ^ 70 +
        8153059565081415834221613997987142070675040474712656420759736617353969) * 10 ^ 70 +
        0137089002658235798071968872013048870475271187199013004366720385256781) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_133 :
    recurrence2Scalar4Main.coeff 133 =
      -(((1393027335762520473912765172838 * 10 ^ 70 +
        3262750136816181382578014371999710977573332830032571070341792130891581) * 10 ^ 70 +
        0886031072914482547034023874558249889226256928114604144943701671409774) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_134 :
    recurrence2Scalar4Main.coeff 134 =
      -(((1857344820691942933900250089127 * 10 ^ 70 +
        1148077623560742351392574908203229574847733057232979293409874740977478) * 10 ^ 70 +
        3225699855204554261199025168959627666226565548432213897609319032321145) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_135 :
    recurrence2Scalar4Main.coeff 135 =
      (((17654820396919779607279819831317 * 10 ^ 70 +
        3505745334808618773819419232272597790134351383182472099346203409813259) * 10 ^ 70 +
        3805815071448549411631189988127662981916089967458402357892026715018279) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_136 :
    recurrence2Scalar4Main.coeff 136 =
      -(((20217597998976408683259720717314 * 10 ^ 70 +
        6888876666838218593968045514509810237800670422499209520724468212031188) * 10 ^ 70 +
        5664671640867935426718335658415760103085005314493133243543252104179138) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_137 :
    recurrence2Scalar4Main.coeff 137 =
      -(((170923283153777121146149758851099 * 10 ^ 70 +
        3061080390127007280218577972971863241647835185179648671417043114787277) * 10 ^ 70 +
        1248686690687623239349694771720852610299582566756905926032807375476822) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

theorem recurrence2Scalar4Main_coeff_138 :
    recurrence2Scalar4Main.coeff 138 =
      (((691089731476049364355603607156688 * 10 ^ 70 +
        5811897429392581677753870877944045336669460945842608222221011825551495) * 10 ^ 70 +
        5843795846566426755252594037374803835722570019398895034329884220389845) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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

private theorem recurrence2Scalar4Main_coeff_139_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (139 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_139 :
    recurrence2Scalar4Main.coeff 139 =
      (((765608942161927678326719220307323 * 10 ^ 70 +
        4819052234854721907113556195385558009776047345505233822557528040761680) * 10 ^ 70 +
        4288131984118097678069255421238262538305681579062675314864801509218053) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_139_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_140_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (140 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_140 :
    recurrence2Scalar4Main.coeff 140 =
      -(((14051473680258765386753550922316957 * 10 ^ 70 +
        4095637989418848430476025500568089894216503687363508333715304544728202) * 10 ^ 70 +
        8440972135307300899860220145701791874753275095560669167355215956302427) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 13 = 11 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_140_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_141_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (141 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_141 :
    recurrence2Scalar4Main.coeff 141 =
      (((41300994968632911731373512890196883 * 10 ^ 70 +
        2632099360299445657175394525883032823566291724698297578178984098949548) * 10 ^ 70 +
        8719977542081448353221836022473586075664244335006323683092483459264440) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 14 = 11 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_141_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_142_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (142 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_142 :
    recurrence2Scalar4Main.coeff 142 =
      (((34212195103267637136611821626131542 * 10 ^ 70 +
        6390746893302748363161212333159156106398086814987558964606900245083632) * 10 ^ 70 +
        0106418300131693327593086875348511615187377048174258503988773049167532) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 15 = 11 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_142_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (143 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_143 :
    recurrence2Scalar4Main.coeff 143 =
      -(((578041423345630196095782398349781776 * 10 ^ 70 +
        3116918675950860222422898420059467155254299738977237617802397768039386) * 10 ^ 70 +
        9379430458808270354010539361091120023042962555324663007502979815705193) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 16 = 11 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (144 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_144 :
    recurrence2Scalar4Main.coeff 144 =
      (((1160199372130292638274781742659750974 * 10 ^ 70 +
        8973936482836889494000148260939794988515048513517229589669601109380582) * 10 ^ 70 +
        1127224859414605916694980451744618688677372845716546969456247296311805) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 17 = 11 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (145 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_145 :
    recurrence2Scalar4Main.coeff 145 =
      (((4001583468657955700598316175634554037 * 10 ^ 70 +
        7018315955073232596684125062335047328999226983678289581394689541230967) * 10 ^ 70 +
        8253797987769633554889858530924896851477950964895201671538982122567583) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 18 = 11 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (146 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_146 :
    recurrence2Scalar4Main.coeff 146 =
      -(((24464639848031059937466383865746064496 * 10 ^ 70 +
        2704296145483668083183743723275836474674807297803679581025706250654881) * 10 ^ 70 +
        7749253028637847552976212854378963175122852091254575563663940381631323) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 19 = 11 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (147 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_147 :
    recurrence2Scalar4Main.coeff 147 =
      (((3091509336681512360182351572511661827 * 10 ^ 70 +
        6900914257724530906361528090565887928660381229058199452595682091300031) * 10 ^ 70 +
        9746845441709154116275917536486153282190466442983424566788735623003572) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 20 = 11 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (148 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_148 :
    recurrence2Scalar4Main.coeff 148 =
      (((389577339830305751482501312618877638492 * 10 ^ 70 +
        8139504195992559371646268609442604876163588557054054054019196006130687) * 10 ^ 70 +
        4162735510905251662776668825828802429557938779745831529627733640346758) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 21 = 11 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (149 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_149 :
    recurrence2Scalar4Main.coeff 149 =
      -(((1435311722321903520386131861573005443345 * 10 ^ 70 +
        8068204551773562345868385624719647942618498307530387915349574015420518) * 10 ^ 70 +
        0601889384184832334771008400010339600922922947902493859381973611360248) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 22 = 11 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (150 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_150 :
    recurrence2Scalar4Main.coeff 150 =
      -(((690144919464870399618404483399800834641 * 10 ^ 70 +
        3590920690810510166126186169262239738815376732026752766595131561816133) * 10 ^ 70 +
        6553628865436826789076017914072652304386301575081589048818897639919398) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 23 = 11 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (151 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_151 :
    recurrence2Scalar4Main.coeff 151 =
      (((24174648076990437804769601221060907118107 * 10 ^ 70 +
        5141028058389917132214490164717154943608204489349834082625831853884368) * 10 ^ 70 +
        5567350627375411318202279411971639306133333453742017656865691695352472) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 24 = 11 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (152 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_152 :
    recurrence2Scalar4Main.coeff 152 =
      -(((84668028530269297165211641640197689799593 * 10 ^ 70 +
        5551602532586496221857909638866742783751297289984724741081018521433847) * 10 ^ 70 +
        9730097032118042623833195023277904551550529644916399479032387547039901) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 25 = 11 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (153 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_153 :
    recurrence2Scalar4Main.coeff 153 =
      -(((495307400426669427765964668448825103116 * 10 ^ 70 +
        9893299126148358125963598753335041298490291110368554901364606993680440) * 10 ^ 70 +
        1934238512336285604055633139201728841451501966808321476760137766285507) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 26 = 11 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (154 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_154 :
    recurrence2Scalar4Main.coeff 154 =
      (((1122551132307368457358699617034672532549858 * 10 ^ 70 +
        6712641670716419898918324902910462208816596772244982467804026490875506) * 10 ^ 70 +
        4350280774422421458775005445449742119507537549018249023590624793382192) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 27 = 11 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (155 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_155 :
    recurrence2Scalar4Main.coeff 155 =
      -(((4371594050057872579568870026924380945362071 * 10 ^ 70 +
        9833869971792964929591750674313034623670656678240757789353091108350972) * 10 ^ 70 +
        0017346830316509548219346387369607206329238953911720133489944504373254) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 28 = 11 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (156 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_156 :
    recurrence2Scalar4Main.coeff 156 =
      (((3107644577804568733223870572835367316416889 * 10 ^ 70 +
        9338363694825545653515995292953279517481285781462364005437618173759203) * 10 ^ 70 +
        4273619454595891722134830305293334256719164146599428075663590225158144) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 29 = 11 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (157 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_157 :
    recurrence2Scalar4Main.coeff 157 =
      (((40212595492414630420888274903673077253380877 * 10 ^ 70 +
        7191761045235621828006951302332922735741761221397577952364761364816798) * 10 ^ 70 +
        8737221420458901642830089370044764890780458504119964887869814699926144) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 30 = 11 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (158 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_158 :
    recurrence2Scalar4Main.coeff 158 =
      -(((189540430445527651830659357804633628448547913 * 10 ^ 70 +
        9302777533885002222468619163399135813511786179094812992382324483527360) * 10 ^ 70 +
        4158778797098851055080828668476175075388283055159228294148087886053909) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 31 = 11 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (159 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_159 :
    recurrence2Scalar4Main.coeff 159 =
      (((265519806671155147535558081781370419684879312 * 10 ^ 70 +
        4288013060998136775391685580792107450356384582611868822979638137995035) * 10 ^ 70 +
        5942354955971419206823058961302641357923219372844637565225698449998414) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 32 = 11 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (160 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_160 :
    recurrence2Scalar4Main.coeff 160 =
      (((1078767519003143979163300823326425536187550171 * 10 ^ 70 +
        1257560312452916615684187139830858914411242762480007089984894775358800) * 10 ^ 70 +
        7952991786647058280858253720266848607121469014412725692983758592586691) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 33 = 11 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (161 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_161 :
    recurrence2Scalar4Main.coeff 161 =
      -(((6855119820988591383358514042368419041329804143 * 10 ^ 70 +
        7958134255240021249741035366353043323459640726405641323721297474682474) * 10 ^ 70 +
        4652913611669949239551407053459776001848442414993016469905936509267968) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 34 = 11 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (162 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_162 :
    recurrence2Scalar4Main.coeff 162 =
      (((14052329129088213520104095430892009284541068502 * 10 ^ 70 +
        8928235238470862234172845651737733737439207006809257087750649786946082) * 10 ^ 70 +
        9684891599512961492915061379268161726248485174623643174383489387574028) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 35 = 11 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (163 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_163 :
    recurrence2Scalar4Main.coeff 163 =
      (((18744113880128633335110765138693597200203509324 * 10 ^ 70 +
        9842406142320950814363928862378169873600726213560045686978828884990057) * 10 ^ 70 +
        2136007069986285231850702504213297628329026526443391343271411355454163) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 36 = 11 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (164 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_164 :
    recurrence2Scalar4Main.coeff 164 =
      -(((210487391731724416583883875445595732299218252481 * 10 ^ 70 +
        4907852384245118131604084001817079412175082031013756965781867795453411) * 10 ^ 70 +
        9294060968680858572801166702457444757512474597893600658407928389142691) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 37 = 11 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (165 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_165 :
    recurrence2Scalar4Main.coeff 165 =
      (((581750153501658545268955855806677768636766949274 * 10 ^ 70 +
        4850066391896081012913090876011290877217093748381149224497747881591650) * 10 ^ 70 +
        2912815408746200566798043046780885367246018029574209217464769866278926) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 38 = 11 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (166 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_166 :
    recurrence2Scalar4Main.coeff 166 =
      -(((54209499978525458504951506899820640951831272785 * 10 ^ 70 +
        7199549586829224792270239193838351044665712397046068305658809775174420) * 10 ^ 70 +
        1469629929212201928256754243196061157084068054686450247220391000015530) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 39 = 11 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (167 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_167 :
    recurrence2Scalar4Main.coeff 167 =
      -(((5452437032088520311178977310252315174406273839815 * 10 ^ 70 +
        0319796114531508866434647154092147005034079819427505708290713280127559) * 10 ^ 70 +
        2587201483080227177173833485743816148984537187694947238579296528509871) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 40 = 11 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (168 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_168 :
    recurrence2Scalar4Main.coeff 168 =
      (((20509843676340741307283758066754067213044717381222 * 10 ^ 70 +
        7684885464489706208427218166603236858579041844122890008132868067212988) * 10 ^ 70 +
        9119396506607370070224167355874546783415885097536731400132856875647853) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 41 = 11 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (169 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_169 :
    recurrence2Scalar4Main.coeff 169 =
      -(((23752867770371934459423984674543262332730209289913 * 10 ^ 70 +
        6519493197199943466782659219248409004819149831371983271289788112347785) * 10 ^ 70 +
        2569841464553686635251159648917365485560854654428727338083913898671081) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 42 = 11 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (170 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_170 :
    recurrence2Scalar4Main.coeff 170 =
      -(((104440440760961860185571508643891853840840436475889 * 10 ^ 70 +
        5047951192568133454363628513850676876226025186705203052901210408383347) * 10 ^ 70 +
        8028819039285809625044318099616486009201036871179814903960444600829300) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 43 = 11 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (171 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_171 :
    recurrence2Scalar4Main.coeff 171 =
      (((608177495983141179425431176621050395091055628699862 * 10 ^ 70 +
        2207809359577802960040335943220694981194179697007776134409692995365445) * 10 ^ 70 +
        7314445395899321560348420929039851305489821536589931479053744288385857) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 44 = 11 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (172 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_172 :
    recurrence2Scalar4Main.coeff 172 =
      -(((1320338999149375505840735887730937989963755286324320 * 10 ^ 70 +
        1001541382695298561903996480418941142740097896354989533278894862798018) * 10 ^ 70 +
        9035061091256608922149618857800510300719704524970916768880226238326283) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 45 = 11 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (173 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_173 :
    recurrence2Scalar4Main.coeff 173 =
      -(((502597989965711821280639783453863304021951265797682 * 10 ^ 70 +
        2876000204660625280389775341591084120069630707437713091181808021312428) * 10 ^ 70 +
        5587740823845843016309904629168943641474240834320522506183510625184806) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 46 = 11 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (174 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_174 :
    recurrence2Scalar4Main.coeff 174 =
      (((13535320084849810984045516460862121914858422316752838 * 10 ^ 70 +
        3598780277562313752782556614873027003041227031100517802531267879802479) * 10 ^ 70 +
        0243336554697266270641668433697867018276547430473883369257141226491931) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 47 = 11 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (175 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_175 :
    recurrence2Scalar4Main.coeff 175 =
      -(((46718512592209480402466185183104913813083663976260656 * 10 ^ 70 +
        7790293431067199786279833948946764240826408098783990746366666125248188) * 10 ^ 70 +
        1605612290490378877222543313208998398993534068709999377459585505587446) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 48 = 11 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (176 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_176 :
    recurrence2Scalar4Main.coeff 176 =
      (((61512438706801456027024740447268901130481649797278722 * 10 ^ 70 +
        4541517568535904246640032748702753824603127730396355662148785070816429) * 10 ^ 70 +
        9123921389499462492831127433350648174785548181488245629469597883321544) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 49 = 11 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (177 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_177 :
    recurrence2Scalar4Main.coeff 177 =
      (((156950772323936489377023760317558381948586055703051319 * 10 ^ 70 +
        9818935613633406249376502364811123665246906376662350469958778805562943) * 10 ^ 70 +
        1139694781290398665593452852569038123107040739358238341070181567359454) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 50 = 11 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (178 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_178 :
    recurrence2Scalar4Main.coeff 178 =
      -(((1097551334046301716295332455290514346057281084888567540 * 10 ^ 70 +
        0947704012831311259720273130571972559330802778291928111572537185336971) * 10 ^ 70 +
        4836735199428977443353836543467921543830498378044241819382653772350825) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 51 = 11 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (179 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_179 :
    recurrence2Scalar4Main.coeff 179 =
      (((2895704407882056872105671746321250888265199497238006090 * 10 ^ 70 +
        2379203239310739598650245764193784236908763586975102518020060182967384) * 10 ^ 70 +
        6278048215019754879072061647076625775813514645253372877945381834474937) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 52 = 11 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (180 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_180 :
    recurrence2Scalar4Main.coeff 180 =
      -(((2315754562280762373557511872803581896849448909861462389 * 10 ^ 70 +
        2611541250415768384466762052634049011159404642891975318186455816613345) * 10 ^ 70 +
        0180082044854944821553810315747897154067259029324566195618174053395865) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 53 = 11 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (181 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_181 :
    recurrence2Scalar4Main.coeff 181 =
      -(((13640521026892293716924233947827475620322679461564597375 * 10 ^ 70 +
        2801188897063265800816968084469510123332727488019634513433744691016061) * 10 ^ 70 +
        0509917775699962840914867073176347605040994264969375883963557835955135) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 54 = 11 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (182 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_182 :
    recurrence2Scalar4Main.coeff 182 =
      (((69304009252860808794408334775401097065683229608167291996 * 10 ^ 70 +
        2150193077835946771442098934526145758707084201147614985638170424248845) * 10 ^ 70 +
        8177329328115598404325717239522867580180083180798443780738796503451130) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 55 = 11 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (183 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_183 :
    recurrence2Scalar4Main.coeff 183 =
      -(((160916449893783403245660560798679482442800632186575174234 * 10 ^ 70 +
        7185404705210998075000783816661107290359464210677667828229694427252332) * 10 ^ 70 +
        8044392712015030472084560730142479732966464139830960034935013572074529) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 56 = 11 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (184 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_184 :
    recurrence2Scalar4Main.coeff 184 =
      (((101948923573644956289239277029312845852718351095666359935 * 10 ^ 70 +
        1285210041344060632691482907153965972346501537344053308838477185731077) * 10 ^ 70 +
        3655406945680693930177974239093383908284378117513439896720676886771214) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 57 = 11 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (185 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_185 :
    recurrence2Scalar4Main.coeff 185 =
      (((773490434954409666115680366455211187084592553141132269093 * 10 ^ 70 +
        0140390783260469708511450200914881463103354693685890834286870191835513) * 10 ^ 70 +
        0490188834810151021260571044575538151699006726236853789536737886545022) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 58 = 11 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (186 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_186 :
    recurrence2Scalar4Main.coeff 186 =
      -(((3662885241568676665214666490984469427562719788201960794176 * 10 ^ 70 +
        5549864158992604587086658780162356368366814481751423230316969508131873) * 10 ^ 70 +
        1647320273726573100940886542899874727940632444290903516656125749737670) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 59 = 11 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (187 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_187 :
    recurrence2Scalar4Main.coeff 187 =
      (((8550030963865126837526849010925838976554099087844615435456 * 10 ^ 70 +
        3919825149665236311574093628517522954205046431158341254445841182863436) * 10 ^ 70 +
        9718952556701174033500416460560104276582612143377754106634987768280774) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 60 = 11 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (188 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_188 :
    recurrence2Scalar4Main.coeff 188 =
      -(((7502334676632039393343639408111910043211506573286294999053 * 10 ^ 70 +
        2065109084891940562381538181061066695430675647753014145174773344132620) * 10 ^ 70 +
        6964470633263979494050587015383060825953573343093991977296509523050826) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 61 = 11 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (189 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_189 :
    recurrence2Scalar4Main.coeff 189 =
      -(((28848261526714106782202898309154895102589415277275964807128 * 10 ^ 70 +
        8364260273606338816319916723207844240303703900042129835440461054024173) * 10 ^ 70 +
        2003404378263905340868393746212014089875652506817854475275397905915533) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 62 = 11 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (190 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_190 :
    recurrence2Scalar4Main.coeff 190 =
      (((159485308094492191713214018235598965821197669071012168747346 * 10 ^ 70 +
        7264291250968530090215526404032332193849550907698168504532094654418886) * 10 ^ 70 +
        4701966771802052636903164197364879645224459474270726386239828519200089) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 63 = 11 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (191 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_191 :
    recurrence2Scalar4Main.coeff 191 =
      -(((421622619443554404952825120285842520177865483427739329730380 * 10 ^ 70 +
        5741446247329966037066515117682701297411768016234843388463962334413071) * 10 ^ 70 +
        3123204516085534065253514536284298566417207208081781260325549378507066) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 64 = 11 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (192 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_192 :
    recurrence2Scalar4Main.coeff 192 =
      (((595442742478422790540862986142029941028013673350716158712310 * 10 ^ 70 +
        4596212849631422884359744985128205835848763349567657101939075138255839) * 10 ^ 70 +
        8182084435948249656882941278429881152900653340869862012061584434338289) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 65 = 11 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (193 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_193 :
    recurrence2Scalar4Main.coeff 193 =
      (((356637604802278782534481861122952628524747315583194138607677 * 10 ^ 70 +
        2555135205364082179764794024079141848668726933313758760182060734806642) * 10 ^ 70 +
        2951094965988321409707796470739012571618562451377840412601769931763303) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 66 = 11 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (194 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_194 :
    recurrence2Scalar4Main.coeff 194 =
      -(((5005616538541674126512034976647968451258548335972860733933725 * 10 ^ 70 +
        4360983744485750056588266008514024823810686908491506029641854029125797) * 10 ^ 70 +
        0646322232003253411003384487852037547346956460227066091031593775204909) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 67 = 11 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (195 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_195 :
    recurrence2Scalar4Main.coeff 195 =
      (((16972282629349193790070418129969980534978438353291633144932743 * 10 ^ 70 +
        4702463683075123496397448957584960938237363064388485818760300424131013) * 10 ^ 70 +
        2745046338820000006631744456485249989508628166015240919020890970600822) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 68 = 11 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (196 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_196 :
    recurrence2Scalar4Main.coeff 196 =
      -(((35330546598809857532058602315112329751271560476231583043827784 * 10 ^ 70 +
        8358016929842067533146565222464572782885370449403301293164018757823983) * 10 ^ 70 +
        0534727297353281602464753652895289507977114042232415372149213416785335) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 69 = 11 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (197 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_197 :
    recurrence2Scalar4Main.coeff 197 =
      (((36886451828229405142579893785483572984225594935548891721544666 * 10 ^ 70 +
        0689458877503750295312435353108135873749506030236304072371059041616118) * 10 ^ 70 +
        9083170561980851162503402903773516035365191242732170383176111904376215) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 70 = 11 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (198 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_198 :
    recurrence2Scalar4Main.coeff 198 =
      (((59196412474005496883051113343137771972788911731602769942988009 * 10 ^ 70 +
        2813220399449236371949109501184023501517478925916322374711297535606770) * 10 ^ 70 +
        0878000908646804463898490037045640266419334603864071287609405236352071) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 71 = 11 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (199 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_199 :
    recurrence2Scalar4Main.coeff 199 =
      -(((430462263395051876308629265385714443016343344909976327655037615 * 10 ^ 70 +
        5776860442383060467117924464036181000029678300502398113660930924774394) * 10 ^ 70 +
        2895216729136995302526546702051321542872007357887708173562718342446216) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 72 = 11 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (200 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_200 :
    recurrence2Scalar4Main.coeff 200 =
      (((1319612339968506391153318041833171086039261999280816039491750918 * 10 ^ 70 +
        5946823212108777205429934312486479993045548026791388142330932790209664) * 10 ^ 70 +
        5300118040826173030894331482839743659419610784531106225509364241719540) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 73 = 11 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (201 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_201 :
    recurrence2Scalar4Main.coeff 201 =
      -(((2736672205854154540378726813980123972545919627667761138487091820 * 10 ^ 70 +
        1059278290159295071844879505371474801200233248379374169530047172323069) * 10 ^ 70 +
        2459407191557795741236041446465932538228455442263734050653187836162899) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 74 = 11 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (202 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_202 :
    recurrence2Scalar4Main.coeff 202 =
      (((3541169468720030731959187492738432972374497004505310662644065364 * 10 ^ 70 +
        0174819209985307894054908298848810707745794415818708521151194673636011) * 10 ^ 70 +
        2370823514419504720107623331294930108619138807602949566575812945341419) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 75 = 11 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (203 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_203 :
    recurrence2Scalar4Main.coeff 203 =
      (((489221560446293924382067304111450833867034283519965820054501507 * 10 ^ 70 +
        7680351299707838417159981075391671847587321576969231932957839910740444) * 10 ^ 70 +
        3293192448049473638843974118183069087216986079563216767159910238683388) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 76 = 11 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (204 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_204 :
    recurrence2Scalar4Main.coeff 204 =
      -(((19513071629685158149558348971145478120592317812634633232787056359 * 10 ^ 70 +
        8989897356503300413745657344980496545765823255293071344763523535257415) * 10 ^ 70 +
        0940272431419305507391910209092629739562591109941989529249647762349086) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 77 = 11 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (205 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_205 :
    recurrence2Scalar4Main.coeff 205 =
      (((71564090147867462350814619497270511975724458934488996087508027002 * 10 ^ 70 +
        2533709648260473873949307593335204784776368006720934039414381167524631) * 10 ^ 70 +
        3531978104391101472429064688331793140014358906053851233720968681341489) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 78 = 11 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (206 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_206 :
    recurrence2Scalar4Main.coeff 206 =
      -(((177764928260033109637054267563987071590650099208232511326498264459 * 10 ^ 70 +
        0555697837318634948511187618899609390877902401483906769160533644981068) * 10 ^ 70 +
        1882037768268210964653435163209765818279468642998939184882738935709092) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 79 = 11 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (207 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_207 :
    recurrence2Scalar4Main.coeff 207 =
      (((338188291400152325655720822037482648863331064186641059699306015386 * 10 ^ 70 +
        7344260356038755998568579547503951009183241786283635058304675427723708) * 10 ^ 70 +
        5766178217369981641243301136191449419649923697570244905044997795144680) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 80 = 11 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (208 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_208 :
    recurrence2Scalar4Main.coeff 208 =
      -(((466974333623585108826761650749619474966132758473664984146314660979 * 10 ^ 70 +
        4678358058593334893328877162030289007801296053701608109808744810096175) * 10 ^ 70 +
        5719805403714788546751467682815231757755384957498377795917529110176122) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 81 = 11 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (209 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_209 :
    recurrence2Scalar4Main.coeff 209 =
      (((258765033036518806025245775548447560402612567513828374559083898542 * 10 ^ 70 +
        9838939423243977721124784329537603315400127498973141259334998083729169) * 10 ^ 70 +
        9817851532297948609402279881442155774987539480286854009538014387219459) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 82 = 11 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (210 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_210 :
    recurrence2Scalar4Main.coeff 210 =
      (((1036824822882421268527095061927086341137774389973118862734763011875 * 10 ^ 70 +
        8559896363984433014862217792359278524135633684099314437170813167086861) * 10 ^ 70 +
        3467299291983984694316896393687638315316570102313174542674403540105191) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 83 = 11 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (211 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_211 :
    recurrence2Scalar4Main.coeff 211 =
      -(((4926378202729796066536637050380581375078109000975482993984661691617 * 10 ^ 70 +
        8567084944100304138199065233119159400627921641067404644846533068778917) * 10 ^ 70 +
        6465215470829614558978033396506568211310324973721984632862811469944637) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 84 = 11 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (212 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_212 :
    recurrence2Scalar4Main.coeff 212 =
      (((13993898334596636799403528293241672446770843162633777063694021410402 * 10 ^ 70 +
        6825167569284059315416248897972503614082638391331670879884103179436291) * 10 ^ 70 +
        1566852316040394955716111297113466376982049299374683864947179188576555) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 85 = 11 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (213 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_213 :
    recurrence2Scalar4Main.coeff 213 =
      -(((32040771469225682043105964077981709567567885056530216467838660988512 * 10 ^ 70 +
        2501006190188335674422630023202781094154823588705858601557608956056879) * 10 ^ 70 +
        4329107238556216567540088323100159485510752142406360363084459661323349) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 86 = 11 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (214 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_214 :
    recurrence2Scalar4Main.coeff 214 =
      (((63705467741336647195915285546962385020881388011524300612436978782829 * 10 ^ 70 +
        4077433604869593021827164786642802392342778180042006513060946184199798) * 10 ^ 70 +
        6132368006421539671355290590946899246703396488453912054515736888994869) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 87 = 11 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (215 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_215 :
    recurrence2Scalar4Main.coeff 215 =
      -(((113093178801298498765829387688643798362142934290345129497522263755081 * 10 ^ 70 +
        6752131199231814893292519677367333932385263380318806461269585648834503) * 10 ^ 70 +
        7794030032117735208247169560675251714273462106544195757128858230114936) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 88 = 11 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (216 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_216 :
    recurrence2Scalar4Main.coeff 216 =
      (((180918871548576413265724697274230403995333948733216348170438510064859 * 10 ^ 70 +
        2887451425750768937681065320628362636409711917287691838015739015662604) * 10 ^ 70 +
        7685896353177886329041830804065685329852785237012755009803980142561706) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 89 = 11 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (217 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_217 :
    recurrence2Scalar4Main.coeff 217 =
      -(((259854294532578150075246362015233907701784699842550882654041586321723 * 10 ^ 70 +
        9827568890261866407354151269275336807334851663608687500477430683048069) * 10 ^ 70 +
        4997974699739867569479982039043678995167450922703608192753566560008996) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 90 = 11 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (218 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_218 :
    recurrence2Scalar4Main.coeff 218 =
      (((328260373579093058744661113510228659784648734409583070771067595919758 * 10 ^ 70 +
        0669212485257232600234071813554173560701403297235656900917282138368459) * 10 ^ 70 +
        2797302928077651703539855269449034015961500120430765670650220357220953) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 91 = 11 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (219 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_219 :
    recurrence2Scalar4Main.coeff 219 =
      -(((343288183394694642518484767159498763409328585112194207476196859548726 * 10 ^ 70 +
        9057228444557774781604784662555113627102333083044116807585074147366735) * 10 ^ 70 +
        1029962191645006392860072390954474036564729161290087170947933403466150) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 92 = 11 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (220 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_220 :
    recurrence2Scalar4Main.coeff 220 =
      (((235305201677771155678053165092831706371689525179974524269840110646566 * 10 ^ 70 +
        1470870972655057315305471748037949387518756161524335518131275374528073) * 10 ^ 70 +
        5955526672136428180376209501660836072097295340282383628430863454132198) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 93 = 11 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (221 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_221 :
    recurrence2Scalar4Main.coeff 221 =
      (((93563043618153505547987815469175528917862493966508441682046602246497 * 10 ^ 70 +
        6573759812410943850503366507515848892714449736891180000760402692043623) * 10 ^ 70 +
        4077717065167199132963225938444037459468445567021844531860048498381486) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
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
    rw [show 94 = 11 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (222 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_222 :
    recurrence2Scalar4Main.coeff 222 =
      -(((763730577712869530213127500442131311435163203710292713817442438124997 * 10 ^ 70 +
        3260647150083108505906268633293325517873662880972683566606457838709393) * 10 ^ 70 +
        4098337572981833972819264268851181329971485002052846901929476366052717) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 0 +
    223 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
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
    rw [show 95 = 11 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (223 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_223 :
    recurrence2Scalar4Main.coeff 223 =
      (((1902992841808837530681720373615730696895554451786700683757792747131934 * 10 ^ 70 +
        5722343140719724962984034578010063941247814020986145398570061788303518) * 10 ^ 70 +
        5209822766404628608870599263910639079801487441219081938719315533888709) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 0 +
    224 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
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
    rw [show 96 = 11 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (224 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_224 :
    recurrence2Scalar4Main.coeff 224 =
      -(((3621588019868893534226399203726696846962191125348141860199757201225155 * 10 ^ 70 +
        5115145214126933946649652303613929414930900979073848118101426634128625) * 10 ^ 70 +
        1682063874542512393475052183028630087333780553686890831499131854915041) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 0 +
    225 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
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
    rw [show 97 = 11 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (225 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_225 :
    recurrence2Scalar4Main.coeff 225 =
      (((5980147142530380927333991879646105341086702088150201682316148990371873 * 10 ^ 70 +
        6290959905501195228790557893439584884132004212442658782184555611574217) * 10 ^ 70 +
        1064495508243630573591445853715956371559381075083357742921566564767507) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 0 +
    226 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
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
    rw [show 98 = 11 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (226 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_226 :
    recurrence2Scalar4Main.coeff 226 =
      -(((8956523768613645238369057059153073367233132260721689172002621162743652 * 10 ^ 70 +
        9587003286992281080806566750210100338738235997203311878482302856743366) * 10 ^ 70 +
        5093463876250747535686966542280016440105527041975301656712509079009451) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 0 +
    227 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
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
    rw [show 99 = 11 +
      88 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (227 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_227 :
    recurrence2Scalar4Main.coeff 227 =
      ((((1 * 10 ^ 70 +
        2420048692817636811046743994304587802198310426922111435481984659600225) * 10 ^ 70 +
        9086345866081550397922994502678499476442582931364162811203386706410993) * 10 ^ 70 +
        3636345061351638095959309287405349904302017721146072850068508326044690) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 0 +
    228 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
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
    rw [show 100 = 11 +
      89 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (228 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_228 :
    recurrence2Scalar4Main.coeff 228 =
      -((((1 * 10 ^ 70 +
        6122368946936604984980984948236427585774543964093263579333492276600482) * 10 ^ 70 +
        0160908315379607190125997537194160526036315160594297969402623508426330) * 10 ^ 70 +
        0665970738898403089255058358519099734699725304192107092617996487771553) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 0 +
    229 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
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
    rw [show 101 = 11 +
      90 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (229 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_229 :
    recurrence2Scalar4Main.coeff 229 =
      ((((1 * 10 ^ 70 +
        9711904799407735771481095837912624600697049920145212038489178352857498) * 10 ^ 70 +
        8589141170691503070699225797237842027687785626831679726205062589350618) * 10 ^ 70 +
        3766889142527414550121429840699478957965422425450121011308195662593377) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 0 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
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
    rw [show 102 = 11 +
      91 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (230 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_230 :
    recurrence2Scalar4Main.coeff 230 =
      -((((2 * 10 ^ 70 +
        2774095033267714646538919063841421400589161295907506935971233836419975) * 10 ^ 70 +
        6139048825416294894464374878699036156376562673503691256263887910265457) * 10 ^ 70 +
        4965471653146423774907924098788641556815961209744665495550353397846622) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 0 +
    231 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
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
    rw [show 103 = 11 +
      92 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (231 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_231 :
    recurrence2Scalar4Main.coeff 231 =
      ((((2 * 10 ^ 70 +
        4892996607894148789467920867950578824466032546248167817965652775744140) * 10 ^ 70 +
        6213819982119581026608594652125917058496073595136145036570427488046108) * 10 ^ 70 +
        7747977165927669436679894534308661636081828987227028083363705295884986) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 0 +
    232 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
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
    rw [show 104 = 11 +
      93 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar4Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient4.coeff (139 + x) *
        recurrence2QuotientConstant.coeff (232 - (139 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B4_coeff_high (139 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Main_coeff_232 :
    recurrence2Scalar4Main.coeff 232 =
      -((((2 * 10 ^ 70 +
        5723280489061886330056861171536976452641346188235717082266230782392539) * 10 ^ 70 +
        8410852488596618025254023693770570958913017039134882237644087830296447) * 10 ^ 70 +
        4551006252388443808618392084716443150570734161627146502879730711672511) : ℚ) := by
  unfold recurrence2Scalar4Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 0 +
    233 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
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
    rw [show 105 = 11 +
      94 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Main_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
