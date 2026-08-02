/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B3_coeff_0
  recurrence2B3_coeff_1
  recurrence2B3_coeff_2
  recurrence2B3_coeff_3
  recurrence2B3_coeff_4
  recurrence2B3_coeff_5
  recurrence2B3_coeff_6
  recurrence2B3_coeff_7
  recurrence2B3_coeff_8
  recurrence2B3_coeff_9
  recurrence2B3_coeff_10
  recurrence2B3_coeff_11
  recurrence2B3_coeff_12
  recurrence2B3_coeff_13
  recurrence2B3_coeff_14
  recurrence2B3_coeff_15
  recurrence2B3_coeff_16
  recurrence2B3_coeff_17
  recurrence2B3_coeff_18
  recurrence2B3_coeff_19
  recurrence2B3_coeff_20
  recurrence2B3_coeff_21
  recurrence2B3_coeff_22
  recurrence2B3_coeff_23
  recurrence2B3_coeff_24
  recurrence2B3_coeff_25
  recurrence2B3_coeff_26
  recurrence2B3_coeff_27
  recurrence2B3_coeff_28
  recurrence2B3_coeff_29
  recurrence2B3_coeff_30
  recurrence2B3_coeff_31
  recurrence2B3_coeff_32
  recurrence2B3_coeff_33
  recurrence2B3_coeff_34
  recurrence2B3_coeff_35
  recurrence2B3_coeff_36
  recurrence2B3_coeff_37
  recurrence2B3_coeff_38
  recurrence2B3_coeff_39
  recurrence2B3_coeff_40
  recurrence2B3_coeff_41
  recurrence2B3_coeff_42
  recurrence2B3_coeff_43
  recurrence2B3_coeff_44
  recurrence2B3_coeff_45
  recurrence2B3_coeff_46
  recurrence2B3_coeff_47
  recurrence2B3_coeff_48
  recurrence2B3_coeff_49
  recurrence2B3_coeff_50
  recurrence2B3_coeff_51
  recurrence2B3_coeff_52
  recurrence2B3_coeff_53
  recurrence2B3_coeff_54
  recurrence2B3_coeff_55
  recurrence2B3_coeff_56
  recurrence2B3_coeff_57
  recurrence2B3_coeff_58
  recurrence2B3_coeff_59
  recurrence2B3_coeff_60
  recurrence2B3_coeff_61
  recurrence2B3_coeff_62
  recurrence2B3_coeff_63
  recurrence2B3_coeff_64
  recurrence2B3_coeff_65
  recurrence2B3_coeff_66
  recurrence2B3_coeff_67
  recurrence2B3_coeff_68
  recurrence2B3_coeff_69
  recurrence2B3_coeff_70
  recurrence2B3_coeff_71
  recurrence2B3_coeff_72
  recurrence2B3_coeff_73
  recurrence2B3_coeff_74
  recurrence2B3_coeff_75
  recurrence2B3_coeff_76
  recurrence2B3_coeff_77
  recurrence2B3_coeff_78
  recurrence2B3_coeff_79
  recurrence2B3_coeff_80
  recurrence2B3_coeff_81
  recurrence2B3_coeff_82
  recurrence2B3_coeff_83
  recurrence2B3_coeff_84
  recurrence2B3_coeff_85
  recurrence2B3_coeff_86
  recurrence2B3_coeff_87
  recurrence2B3_coeff_88
  recurrence2B3_coeff_89
  recurrence2B3_coeff_90
  recurrence2B3_coeff_91
  recurrence2B3_coeff_92
  recurrence2B3_coeff_93
  recurrence2B3_coeff_94
  recurrence2B3_coeff_95
  recurrence2B3_coeff_96
  recurrence2B3_coeff_97
  recurrence2B3_coeff_98
  recurrence2B3_coeff_99
  recurrence2B3_coeff_100
  recurrence2B3_coeff_101
  recurrence2B3_coeff_102
  recurrence2B3_coeff_103
  recurrence2B3_coeff_104
  recurrence2B3_coeff_105
  recurrence2B3_coeff_106
  recurrence2B3_coeff_107
  recurrence2B3_coeff_108
  recurrence2B3_coeff_109
  recurrence2B3_coeff_110
  recurrence2B3_coeff_111
  recurrence2B3_coeff_112
  recurrence2B3_coeff_113
  recurrence2B3_coeff_114
  recurrence2B3_coeff_115
  recurrence2B3_coeff_116
  recurrence2B3_coeff_117
  recurrence2B3_coeff_118
  recurrence2B3_coeff_119
  recurrence2B3_coeff_120
  recurrence2B3_coeff_121
  recurrence2B3_coeff_122
  recurrence2B3_coeff_123
  recurrence2B3_coeff_124
  recurrence2B3_coeff_125
  recurrence2B3_coeff_126
  recurrence2B3_coeff_127
  recurrence2B3_coeff_128
  recurrence2B3_coeff_129
  recurrence2B3_coeff_130
  recurrence2B3_coeff_131
  recurrence2B3_coeff_132
  recurrence2B3_coeff_133
  recurrence2B3_coeff_134
  recurrence2B3_coeff_135
  recurrence2B3_coeff_136
  recurrence2B3_coeff_137
  recurrence2B3_coeff_138
  recurrence2B3_coeff_139
  recurrence2B3_coeff_140
  recurrence2B3_coeff_141
  recurrence2B3_coeff_142
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

theorem recurrence2Scalar3Main_coeff_0 :
    recurrence2Scalar3Main.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_1 :
    recurrence2Scalar3Main.coeff 1 =
      (-245760 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_2 :
    recurrence2Scalar3Main.coeff 2 =
      (-1311992320 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_3 :
    recurrence2Scalar3Main.coeff 3 =
      (15309813383136 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_4 :
    recurrence2Scalar3Main.coeff 4 =
      (75631528883148544 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_5 :
    recurrence2Scalar3Main.coeff 5 =
      (271674164254755462272 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_6 :
    recurrence2Scalar3Main.coeff 6 =
      (51568935578271997340632 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_7 :
    recurrence2Scalar3Main.coeff 7 =
      (394764270841824131681727984 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_8 :
    recurrence2Scalar3Main.coeff 8 =
      (-58088187846002845877333521560 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_9 :
    recurrence2Scalar3Main.coeff 9 =
      (4354756223246642437773912829632 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_10 :
    recurrence2Scalar3Main.coeff 10 =
      (-325644257316674834181757354723616 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_11 :
    recurrence2Scalar3Main.coeff 11 =
      (-23602872492138760706393068834941981282 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_12 :
    recurrence2Scalar3Main.coeff 12 =
      (13265522306052799426670269555122825978344 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_13 :
    recurrence2Scalar3Main.coeff 13 =
      (-6330471829925992442926744533082033760930028 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_14 :
    recurrence2Scalar3Main.coeff 14 =
      (1922287186365074682972795392149898577288561856 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_15 :
    recurrence2Scalar3Main.coeff 15 =
      (-444247922720559587497894708827731257275215626371 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_16 :
    recurrence2Scalar3Main.coeff 16 =
      (78480218586310739943961266428842541323090812784831 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_17 :
    recurrence2Scalar3Main.coeff 17 =
      (-10710283776665076329832858548470947425732812068078443 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_18 :
    recurrence2Scalar3Main.coeff 18 =
      (1126575424414204354197440921581550758587724833659305554 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_19 :
    recurrence2Scalar3Main.coeff 19 =
      (-88073231685375457542935853044498048485253862089421839547 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_20 :
    recurrence2Scalar3Main.coeff 20 =
      (4683015102321041169192232790198483407446974306383909308421 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_21 :
    recurrence2Scalar3Main.coeff 21 =
      (-104284078421291561932768727206338131440827945483353340761144 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_22 :
    recurrence2Scalar3Main.coeff 22 =
      (-7579946663234040830810074100376587993754108563103976680955241 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_23 :
    recurrence2Scalar3Main.coeff 23 =
      (901759311704842513829284094333003996486686541286904865385320195 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_24 :
    recurrence2Scalar3Main.coeff 24 =
      (-35729763379853399161267607759076708586457891815405780244323280779 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_25 :
    recurrence2Scalar3Main.coeff 25 =
      (-1000263313359525976321882487756350780577972402473385342015745054109 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_26 :
    recurrence2Scalar3Main.coeff 26 =
      (243398801024327857543664047081766683664295359819489144324955638204646 : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_27 :
    recurrence2Scalar3Main.coeff 27 =
      -((1 * 10 ^ 70 +
        8458003714193447565318022088395281778530070433424433078154780705736229) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_28 :
    recurrence2Scalar3Main.coeff 28 =
      ((80 * 10 ^ 70 +
        8255101880701443171687727983152638435968872145198849602159849579894179) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_29 :
    recurrence2Scalar3Main.coeff 29 =
      -((1140 * 10 ^ 70 +
        3188351929780232647906802221570056793279724912920014630455687188002170) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_30 :
    recurrence2Scalar3Main.coeff 30 =
      -((142778 * 10 ^ 70 +
        1376282949187815216754182858140932403774993570342289704659789148476618) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_31 :
    recurrence2Scalar3Main.coeff 31 =
      ((14504545 * 10 ^ 70 +
        3840987844428104717738891567373082599718892282773422786595403871638193) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_32 :
    recurrence2Scalar3Main.coeff 32 =
      -((733501814 * 10 ^ 70 +
        5262815492264368213200804537689189653643637339717844660672814109923430) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_33 :
    recurrence2Scalar3Main.coeff 33 =
      ((17513217870 * 10 ^ 70 +
        2420286179397995954377947975549108004121029192110699295955458197358812) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_34 :
    recurrence2Scalar3Main.coeff 34 =
      ((563078368443 * 10 ^ 70 +
        5898730253253831971385024523876314299672471354373526816730286309530464) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_35 :
    recurrence2Scalar3Main.coeff 35 =
      -((87423553119555 * 10 ^ 70 +
        1521522396198998363542726331492141168799244108619885383950729745224828) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_36 :
    recurrence2Scalar3Main.coeff 36 =
      ((5501889379195231 * 10 ^ 70 +
        6106027895961654574939918872160719874588556597038533785623371079167032) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_37 :
    recurrence2Scalar3Main.coeff 37 =
      -((241319835167300312 * 10 ^ 70 +
        8294454578014080453863030482897267495788396044565339777043010091064772) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_38 :
    recurrence2Scalar3Main.coeff 38 =
      ((8075979082654781860 * 10 ^ 70 +
        8766347180000188106125150110346017907890272699505358504010897349763398) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_39 :
    recurrence2Scalar3Main.coeff 39 =
      -((208300368214149398159 * 10 ^ 70 +
        5326557497581885308067567661123185867630603967326002037800575258611638) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_40 :
    recurrence2Scalar3Main.coeff 40 =
      ((3942655720847704878625 * 10 ^ 70 +
        5164392491488193638549875504047435697294938088811547704702249784915514) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_41 :
    recurrence2Scalar3Main.coeff 41 =
      -((44153111236255400919835 * 10 ^ 70 +
        4506785300120363135726449581498728512542521746808155578769547758173590) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_42 :
    recurrence2Scalar3Main.coeff 42 =
      -((148018050700570702956362 * 10 ^ 70 +
        1786402723130927099878641160709430505784925978449582069348329731218404) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_43 :
    recurrence2Scalar3Main.coeff 43 =
      ((17908834076533072589016357 * 10 ^ 70 +
        2595302901545484311190590312119363408953692739757401375885946551114293) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_44 :
    recurrence2Scalar3Main.coeff 44 =
      -((325216933841026665200983882 * 10 ^ 70 +
        6386654460486778361360616282066864735101419308037953239446613884544289) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_45 :
    recurrence2Scalar3Main.coeff 45 =
      -((487852107054551946007278509 * 10 ^ 70 +
        8881169015385282169221203014932097400544560292323735410588162285078209) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_46 :
    recurrence2Scalar3Main.coeff 46 =
      ((157882416744305531094111040086 * 10 ^ 70 +
        1814970612897287895904074069738881441170709221299908436322628114983398) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_47 :
    recurrence2Scalar3Main.coeff 47 =
      -((3178070250341754040243755261061 * 10 ^ 70 +
        3577627538204263624432512982284477545940339842760115920483591367028210) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_48 :
    recurrence2Scalar3Main.coeff 48 =
      -((25689603788054134668600257392225 * 10 ^ 70 +
        4839595200611279246810047050916878156588007739015235173558973552588756) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_49 :
    recurrence2Scalar3Main.coeff 49 =
      ((3594658928979383000695485057755748 * 10 ^ 70 +
        3438115603127321094795891108884967312939329129190119156393922171769229) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_50 :
    recurrence2Scalar3Main.coeff 50 =
      -((133765867343342917505890315501497897 * 10 ^ 70 +
        3416957986207080067425456056754560881748589991326444424758566229233287) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_51 :
    recurrence2Scalar3Main.coeff 51 =
      ((3420234522222403472599471298875946272 * 10 ^ 70 +
        8946301449010154294663281788752747631665996545354268880164141334465938) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_52 :
    recurrence2Scalar3Main.coeff 52 =
      -((69106315696247092605933880251695264303 * 10 ^ 70 +
        2199499718038458190911127592695048624393923717356530349738965960297088) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_53 :
    recurrence2Scalar3Main.coeff 53 =
      ((1153424444419026053450213911370233093261 * 10 ^ 70 +
        4275885047114291701611856704678823338808265924110721169756322972757240) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_54 :
    recurrence2Scalar3Main.coeff 54 =
      -((15889720578160343529594999037423083427738 * 10 ^ 70 +
        8696551912231595968090682591365739731478042025337762417820953236432832) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_55 :
    recurrence2Scalar3Main.coeff 55 =
      ((167737360310022384295187121764025475388700 * 10 ^ 70 +
        4488795935151003688695875501852358164852548567219339896845361355471372) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_56 :
    recurrence2Scalar3Main.coeff 56 =
      -((834878349824233133943970738815337423211187 * 10 ^ 70 +
        5623168198033480414896646162700804175696700525944822201286616739052500) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_57 :
    recurrence2Scalar3Main.coeff 57 =
      -((18614194096183298039959873750837109495746896 * 10 ^ 70 +
        5021588273088444452443266932573463092871841379336482532963011654443851) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_58 :
    recurrence2Scalar3Main.coeff 58 =
      ((765214652499646783916608851875444568635604610 * 10 ^ 70 +
        2379636872651892656448747197452267519096518217252382725534332834762989) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_59 :
    recurrence2Scalar3Main.coeff 59 =
      -((17830021007412740676263924828713164150478634333 * 10 ^ 70 +
        9668322996197399993480223094514980148383492494370004662033431519057909) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_60 :
    recurrence2Scalar3Main.coeff 60 =
      ((331310038798715851688869252673524609802425419730 * 10 ^ 70 +
        9402354061217405138578092783727952819646419397720522163542073995198160) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_61 :
    recurrence2Scalar3Main.coeff 61 =
      -((5288387483601610191807282987241243066749084134357 * 10 ^ 70 +
        2310876688318849113455640322660424603672656763482537819653208891224427) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_62 :
    recurrence2Scalar3Main.coeff 62 =
      ((74277414660947702584209974972533762969212731151462 * 10 ^ 70 +
        5043309773770934785476208309953198236701429652469570178931236790727930) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_63 :
    recurrence2Scalar3Main.coeff 63 =
      -((922147780911870948127518066521202227131300462659690 * 10 ^ 70 +
        4767053980232582951711032636473590427434838980047164689083631759709991) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_64 :
    recurrence2Scalar3Main.coeff 64 =
      ((10004940697351475191825332483505154064274533804325068 * 10 ^ 70 +
        9989166133704868780619773018049614467353324367944612122440804715650718) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_65 :
    recurrence2Scalar3Main.coeff 65 =
      -((91110929153882400569014551786448622878585253584825304 * 10 ^ 70 +
        2503208452190615586132456801031730492750271318929583554272575146688341) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_66 :
    recurrence2Scalar3Main.coeff 66 =
      ((605723289506369087678931661703864219638035348039281349 * 10 ^ 70 +
        5816040082431347823376381550503534174673435249987672642918198509090544) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_67 :
    recurrence2Scalar3Main.coeff 67 =
      -((707669801987491593810273341508215908419619099807908309 * 10 ^ 70 +
        9789205427394706836825169721067312940444150187386898370941357214632410) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_68 :
    recurrence2Scalar3Main.coeff 68 =
      -((66361154567105791223020280951479479659231001700886194703 * 10 ^ 70 +
        9330037543811599035898916484089379577741422437413131637733552585556900) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_69 :
    recurrence2Scalar3Main.coeff 69 =
      ((1524581352927181922033976438412367204556372094661178490485 * 10 ^ 70 +
        4396669084445293364625410623623789136992571662652549880985227556633600) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_70 :
    recurrence2Scalar3Main.coeff 70 =
      -((24082441776638628436236131725558123158904284495816524641763 * 10 ^ 70 +
        8863104061912882329806323620152391949635140858288180109288352303677968) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_71 :
    recurrence2Scalar3Main.coeff 71 =
      ((319981957108878818665488835012985479296853833997172887910061 * 10 ^ 70 +
        2717511505269486028909038392885734058888495282598687380272430362526942) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_72 :
    recurrence2Scalar3Main.coeff 72 =
      -((3797615266186443600656545844375942992293840121251640799169988 * 10 ^ 70 +
        9503950125731146350549275216408063846381046306290146077020808410188632) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_73 :
    recurrence2Scalar3Main.coeff 73 =
      ((41340776516153804701991082569869546463250745823311297649728439 * 10 ^ 70 +
        2503312607967270118570587086194083302744938317292107715570050644390344) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_74 :
    recurrence2Scalar3Main.coeff 74 =
      -((418766817035324663714854191111524590185036232727185670315344279 * 10 ^ 70 +
        7291647307452942428819570258516206052567788798123925342929360399281734) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_75 :
    recurrence2Scalar3Main.coeff 75 =
      ((3982516472627718637649389027816136742435452691805403540693978538 * 10 ^ 70 +
        3540512003576917614622709304579917914012773583520888781072815650339289) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_76 :
    recurrence2Scalar3Main.coeff 76 =
      -((35772901203534890970652297433613340045179301182042547880830778267 * 10 ^ 70 +
        3035732035202731997357439169363321408853377237389441905980054331443799) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_77 :
    recurrence2Scalar3Main.coeff 77 =
      ((304816307088226381429220524214338299806416130121864222487305496621 * 10 ^ 70 +
        5203402047871717633953163653822801295752493993664076102863747485672175) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_78 :
    recurrence2Scalar3Main.coeff 78 =
      -((2471669456544676759824767268595084137972625308667788995328269285611 * 10 ^ 70 +
        2251943279044739825876588252785238211776171328221231516565164583620607) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_79 :
    recurrence2Scalar3Main.coeff 79 =
      ((19117764382591653848727237650198034299579412829623393691709594181687 * 10 ^ 70 +
        6044627074734369696987149608755777796572018192105009393366339375849232) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_80 :
    recurrence2Scalar3Main.coeff 80 =
      -((141301888830277807391794390714681700826531076660018973532432258506188 * 10 ^ 70 +
        2277532928165228491333780742128357456439494856955784105935296439122255) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_81 :
    recurrence2Scalar3Main.coeff 81 =
      ((999341727611627107350634841081280675251489912335934674727830547373700 * 10 ^ 70 +
        1702405589150329256617225173326219119691032178436903490682637116099696) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_82 :
    recurrence2Scalar3Main.coeff 82 =
      -((6770339176035814903189342414514032683032991831412257118616850578085321 * 10 ^ 70 +
        8732677033736694458609881885005304516277749475158774706338028298405228) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_83 :
    recurrence2Scalar3Main.coeff 83 =
      (((4 * 10 ^ 70 +
        3978355075972550212350258695276509098747709840058443361851905362054427) * 10 ^ 70 +
        2703184587955548833873257343716886709547124145005172537605632431543053) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_84 :
    recurrence2Scalar3Main.coeff 84 =
      -(((27 * 10 ^ 70 +
        4122871150705538237390564269945971351491235739202216709156643887264774) * 10 ^ 70 +
        4780028998422874059765383960170897230420357042839679286530782710318134) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_85 :
    recurrence2Scalar3Main.coeff 85 =
      (((164 * 10 ^ 70 +
        0629366693320983062116141341673005770526214350849685690069845576223586) * 10 ^ 70 +
        6018567684340532884215781492187250760132540142515907776164366193779428) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_86 :
    recurrence2Scalar3Main.coeff 86 =
      -(((943 * 10 ^ 70 +
        2481593584546441267097643292023792598908493890321530330005505667795626) * 10 ^ 70 +
        7643216248790363618597657031740189653249684758747332221671708897474253) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_87 :
    recurrence2Scalar3Main.coeff 87 =
      (((5210 * 10 ^ 70 +
        3345960869256264098112254672605545012219275673570816995704599497219609) * 10 ^ 70 +
        1444003754188771737936315199697554940657867083318261795262625665577213) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_88 :
    recurrence2Scalar3Main.coeff 88 =
      -(((27648 * 10 ^ 70 +
        5714411997741965122944441527097976641021710769314753426129634638609847) * 10 ^ 70 +
        1538706063919804213896446904983034307596076831097169289853967688804500) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_89 :
    recurrence2Scalar3Main.coeff 89 =
      (((140887 * 10 ^ 70 +
        2307514964015034376695173348516686156610736447900092359725505306854649) * 10 ^ 70 +
        9219168381439987367659654212494101095162417045797168399219932708191093) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_90 :
    recurrence2Scalar3Main.coeff 90 =
      -(((688970 * 10 ^ 70 +
        7865903080167333034015121548787041144487784217678169583223599419964242) * 10 ^ 70 +
        0651166483111418530904672246537303380317029251393924927449326582680355) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_91 :
    recurrence2Scalar3Main.coeff 91 =
      (((3231055 * 10 ^ 70 +
        0843049410789766319514741882297757340879152264964558918882570548847267) * 10 ^ 70 +
        1288517010305836840704505689675121601264773456134939880068792671076922) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_92 :
    recurrence2Scalar3Main.coeff 92 =
      -(((14518587 * 10 ^ 70 +
        8562852510669818494698714551422713837187027828811042175874312216634628) * 10 ^ 70 +
        2290328757678049121423509148344197970842302144989154682670707302240386) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_93 :
    recurrence2Scalar3Main.coeff 93 =
      (((62431904 * 10 ^ 70 +
        8249695808149033865586851683397268048767430342136858883387326824997311) * 10 ^ 70 +
        3511162177836042669569786973117863407491092151428206678686505371094066) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_94 :
    recurrence2Scalar3Main.coeff 94 =
      -(((256376131 * 10 ^ 70 +
        1799044551664102256731662908902938047494807287261691923492676658754348) * 10 ^ 70 +
        3550370163654748587251942271658538769561577433575843691569124098049941) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_95 :
    recurrence2Scalar3Main.coeff 95 =
      (((1001541069 * 10 ^ 70 +
        4158235246834865932537464071682268446932638741057077729205848474394368) * 10 ^ 70 +
        7120115094745151851879252591949120018134453800625376546193469453015915) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_96 :
    recurrence2Scalar3Main.coeff 96 =
      -(((3696681204 * 10 ^ 70 +
        6597912715157007539619316385216716401241289138228226900740103842055511) * 10 ^ 70 +
        7430868102685416276529551268181318260662785954048033172376926049092276) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_97 :
    recurrence2Scalar3Main.coeff 97 =
      (((12742411180 * 10 ^ 70 +
        1287519252297553677036905251852588142367133329382696223360409073367881) * 10 ^ 70 +
        2854775692607390177229955999020770899420419243043514245963930100990337) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_98 :
    recurrence2Scalar3Main.coeff 98 =
      -(((40219069305 * 10 ^ 70 +
        0910742725276775181870597960373561710659791272589968809523212138659336) * 10 ^ 70 +
        3112884704190973075817782378218487283385641896819582368740806047683953) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_99 :
    recurrence2Scalar3Main.coeff 99 =
      (((112121008196 * 10 ^ 70 +
        0698768354205229017036051251817671187710823423624781729141579412489339) * 10 ^ 70 +
        0786301158818346457018338727334327995312371816176727739509589888844797) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_100 :
    recurrence2Scalar3Main.coeff 100 =
      -(((253985228400 * 10 ^ 70 +
        1595563762190543629278991930476068142347704901279857127854408969327745) * 10 ^ 70 +
        8919626560061831684859719745243686571361802438995736140216204890751135) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_101 :
    recurrence2Scalar3Main.coeff 101 =
      (((331754352210 * 10 ^ 70 +
        8307267421434117247044353274997757927210487209043624739877568664628505) * 10 ^ 70 +
        8739645383103537338082630091534143622408250561223547703543739753211950) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_102 :
    recurrence2Scalar3Main.coeff 102 =
      (((802607510079 * 10 ^ 70 +
        7398565962202874981474657284041635214515060085869893831198750877737938) * 10 ^ 70 +
        9530469476511919355224240171230630458706536855725545531227119887561354) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_103 :
    recurrence2Scalar3Main.coeff 103 =
      -(((9238561004189 * 10 ^ 70 +
        7404558464107213037485427911888187513131615957454217265200394253126908) * 10 ^ 70 +
        1163253045947059214090965708145741074035083152657029687012395984119841) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_104 :
    recurrence2Scalar3Main.coeff 104 =
      (((53722521417974 * 10 ^ 70 +
        5603731172254790884429839583495244316994156932343361663173459140203641) * 10 ^ 70 +
        3638074856816089299963673758954502634610460999755788696644063744643160) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_105 :
    recurrence2Scalar3Main.coeff 105 =
      -(((264152321877351 * 10 ^ 70 +
        2900282502779775489850588752354566583800215696921099019910621092385953) * 10 ^ 70 +
        1672793390043054147245799475351998182157076161937368297738869452912517) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_106 :
    recurrence2Scalar3Main.coeff 106 =
      (((1185482244148706 * 10 ^ 70 +
        9385380900916198442962274897284749654609063324161449901235267381060224) * 10 ^ 70 +
        8104769156346066198503845711322391421923660619126837367208200228444605) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_107 :
    recurrence2Scalar3Main.coeff 107 =
      -(((4769616965309294 * 10 ^ 70 +
        7170464585017868146035018152322378674231957570788962572441250335353300) * 10 ^ 70 +
        0782500231520369695417866300877417290139346095316551602356794801337752) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_108 :
    recurrence2Scalar3Main.coeff 108 =
      (((16151449823017523 * 10 ^ 70 +
        0687481732866208254838455964647823145879382824907561214435656000960822) * 10 ^ 70 +
        9195103125165411819845413342262555582432659012881087742623852131473452) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_109 :
    recurrence2Scalar3Main.coeff 109 =
      -(((40422926546022697 * 10 ^ 70 +
        8373561574300448132759347892635859854024264729734514753753111926891824) * 10 ^ 70 +
        9711407418307207997492517881840960527923768985099120617151638012655844) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_110 :
    recurrence2Scalar3Main.coeff 110 =
      (((42926417253980194 * 10 ^ 70 +
        7284063518675053493169065973707204053758025683519102774150031855007516) * 10 ^ 70 +
        4266089519619734916296946972811426881839544548461306476725295170891033) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_111 :
    recurrence2Scalar3Main.coeff 111 =
      (((193590692312853162 * 10 ^ 70 +
        3652482503320583860728253044351863630398480384654679952423416986686599) * 10 ^ 70 +
        9448457520650359521033991775213472590636596979232211963664882137146870) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_112 :
    recurrence2Scalar3Main.coeff 112 =
      -(((1105041008742517357 * 10 ^ 70 +
        4615699618944508517926059732894149851813092863178478190343074062245453) * 10 ^ 70 +
        5073557931786491913492872562555017736550638813743753022147714842607861) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_113 :
    recurrence2Scalar3Main.coeff 113 =
      (((809230803088070603 * 10 ^ 70 +
        9902780634955044795942029352193719031130990881237758155615692912490064) * 10 ^ 70 +
        6402776591641613872747148268716088491098863300191043866697495413837170) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_114 :
    recurrence2Scalar3Main.coeff 114 =
      (((20686136302528439857 * 10 ^ 70 +
        7880528376948226896510577825220844814978006286548852120569597918099597) * 10 ^ 70 +
        8626602094967825321445215869232579563089131069282721532899511078829181) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_115 :
    recurrence2Scalar3Main.coeff 115 =
      -(((150011280318494127649 * 10 ^ 70 +
        0534374963486727437818914169099335212417213421981880080917958806699398) * 10 ^ 70 +
        4601360704961493174927728268818353127784999145771951303988559524600421) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_116 :
    recurrence2Scalar3Main.coeff 116 =
      (((554902232724285661629 * 10 ^ 70 +
        6584306586872426356918090110401159329106357073237489182895305218454959) * 10 ^ 70 +
        4245511138803884214063098790086976425564101522269537222294961096181358) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_117 :
    recurrence2Scalar3Main.coeff 117 =
      -(((752603357410869913586 * 10 ^ 70 +
        8433283160349679616105900790607243206799249457313758777215735664393304) * 10 ^ 70 +
        5092729657703672721446307960873841348254744107668539693694558221423442) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_118 :
    recurrence2Scalar3Main.coeff 118 =
      -(((5021550490301721084036 * 10 ^ 70 +
        4140936640243550412219180013618736369436712994243327322194572419548215) * 10 ^ 70 +
        6433240017768211463780991166759580910316698907417920455481469779942205) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_119 :
    recurrence2Scalar3Main.coeff 119 =
      (((44252731136220623124830 * 10 ^ 70 +
        3625804466298445454043808916326067728418060643462953797881881264500659) * 10 ^ 70 +
        3631658100036891505901222655636448195078296032288775424814651930556817) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_120 :
    recurrence2Scalar3Main.coeff 120 =
      -(((194859262303352962718765 * 10 ^ 70 +
        3639591835730739802289653262891593034194532011554685029628311590806566) * 10 ^ 70 +
        8946482804716306008557451864953166509474183924009166885668668426803825) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_121 :
    recurrence2Scalar3Main.coeff 121 =
      (((510138315976751262654075 * 10 ^ 70 +
        2711568660626101078347339047291769296735626578288720574976461638718977) * 10 ^ 70 +
        4891483268459271350363391035091044768401725030746713937954828900219051) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_122 :
    recurrence2Scalar3Main.coeff 122 =
      -(((103991941699309448517089 * 10 ^ 70 +
        7416720078422083685056481860811324547428742704060307805315042979691694) * 10 ^ 70 +
        6452414707320792823635648406258461445609633884948583736187878854492377) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_123 :
    recurrence2Scalar3Main.coeff 123 =
      -(((7415614602768394029695298 * 10 ^ 70 +
        7664595339533208719493378145239770945703711690221431074885573245561997) * 10 ^ 70 +
        5833268164058114371236487556571577908587750205590232112646114629462176) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_124 :
    recurrence2Scalar3Main.coeff 124 =
      (((47764746632100822021534536 * 10 ^ 70 +
        5842012458111111558102942333843768025917220703500334124202660678205737) * 10 ^ 70 +
        8308853546219328417068070419322210439045706083258574952925420522046665) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_125 :
    recurrence2Scalar3Main.coeff 125 =
      -(((176993800463363085110742261 * 10 ^ 70 +
        1799021679164722138131386836301237517070094737803099699352668181389751) * 10 ^ 70 +
        8774255336735794936357188220341195323247696411215884087253143692118067) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_126 :
    recurrence2Scalar3Main.coeff 126 =
      (((328853896157706032188029519 * 10 ^ 70 +
        7170347752376091733282045731198255197968377400432300075394720112860275) * 10 ^ 70 +
        5468905915956328994547492331464900436636564080073856715307621986626995) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_127 :
    recurrence2Scalar3Main.coeff 127 =
      (((715662567068876447846446482 * 10 ^ 70 +
        3507543710618289644680559324531730790784284943028799171574791237219237) * 10 ^ 70 +
        8235060658636168205112601640800643482547250159967978373286382291581394) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_128 :
    recurrence2Scalar3Main.coeff 128 =
      -(((8727303629303993762147914916 * 10 ^ 70 +
        5708538136995929801957700467551718106632264080133509779815241621142835) * 10 ^ 70 +
        4900369110452108391170534279211719563908244729578040307022482268207920) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_129 :
    recurrence2Scalar3Main.coeff 129 =
      (((38022797810463428982037935696 * 10 ^ 70 +
        2937632352023830773490180592984706509606213464177465768191146954076570) * 10 ^ 70 +
        1917047420421347102405893518502980741718544288380475238303022464494728) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_130 :
    recurrence2Scalar3Main.coeff 130 =
      -(((91279314275016409772846533616 * 10 ^ 70 +
        5905547275013089675128717571302479372737139168973532490203418036076002) * 10 ^ 70 +
        2140118175038686629237308570060687240889094359467829602305452297188245) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_131 :
    recurrence2Scalar3Main.coeff 131 =
      (((30866523915185462731550551018 * 10 ^ 70 +
        2044498375261905467941790258979608645452955342307707266470860788664886) * 10 ^ 70 +
        2058369633321562748431815698039382031151040002087016271504301587259135) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_132 :
    recurrence2Scalar3Main.coeff 132 =
      (((763714183209683757991564469259 * 10 ^ 70 +
        8064223059111021170976327417817647348466731472486599104116074061905434) * 10 ^ 70 +
        6531174122824404439352189772387275774991905301160612046949697027861276) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_133 :
    recurrence2Scalar3Main.coeff 133 =
      -(((3748328250435713806051280619975 * 10 ^ 70 +
        4418616560500280151979036631272513733445878922834543422355549335361439) * 10 ^ 70 +
        1967357071812224516830736026724644718898933604896014268206200232961023) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_134 :
    recurrence2Scalar3Main.coeff 134 =
      (((10727195613571151068075317728921 * 10 ^ 70 +
        9502933454885186964156034335314745886806958264455877717668385157884178) * 10 ^ 70 +
        6657097850078684517279102217290899815502870734262560302155513737703145) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_135 :
    recurrence2Scalar3Main.coeff 135 =
      -(((22318722491956642279073281191551 * 10 ^ 70 +
        5390256660718267632374993749944350072258475352302408110310250436325607) * 10 ^ 70 +
        9332094162888629164328186593154613188121855239677347835874927093663075) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_136 :
    recurrence2Scalar3Main.coeff 136 =
      (((34447617743424319171426719479021 * 10 ^ 70 +
        4555716311996232062094700170116416148123002851146298804776409543212169) * 10 ^ 70 +
        5928471238567767340865872229555296120372635481991917570228148104749639) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_137 :
    recurrence2Scalar3Main.coeff 137 =
      (((3134466661705030751022175893026 * 10 ^ 70 +
        8853423722244572173912336415154676704949118512166221034356305776363493) * 10 ^ 70 +
        5481975183001343893609244685635555709905650801676988325532620746303005) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_138 :
    recurrence2Scalar3Main.coeff 138 =
      -(((373902250216999132401483030143684 * 10 ^ 70 +
        8700566229306576564714090731332123820273560026003150395604942196952114) * 10 ^ 70 +
        0757588175953148828818139169657585723474956217961811023490906719913567) : ℚ) := by
  unfold recurrence2Scalar3Main
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

theorem recurrence2Scalar3Main_coeff_139 :
    recurrence2Scalar3Main.coeff 139 =
      (((1583306309470495163658509624786207 * 10 ^ 70 +
        4883374246201620596080624943088188541396534274807199188862964959177414) * 10 ^ 70 +
        1836061995490146139632409920020345899875980847725198718878724810493381) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Main_coeff_140 :
    recurrence2Scalar3Main.coeff 140 =
      -(((2087414457228843821255892022606280 * 10 ^ 70 +
        2377242428008831254082013178996991348270959551726685104543484131281374) * 10 ^ 70 +
        0342432604284283523305772705826561107931110532367377098869700381030788) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Main_coeff_141 :
    recurrence2Scalar3Main.coeff 141 =
      (((1051936035552794777483742262996208 * 10 ^ 70 +
        4582202521026695828317954931090621339835632202355835688165762037710701) * 10 ^ 70 +
        6327986238991678894993194500195679430594202991905364387387069602052928) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar3Main_coeff_142 :
    recurrence2Scalar3Main.coeff 142 =
      -(((98257934013621226426278814116372479 * 10 ^ 70 +
        0242881765168990070742697980519127802023234666306875309739722335964324) * 10 ^ 70 +
        4062724733603371088991395352573372132489257013604627376367600363110556) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_143_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (143 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_143 :
    recurrence2Scalar3Main.coeff 143 =
      (((944992973192856228840074105289400946 * 10 ^ 70 +
        4814754599014265037500959259675035260094832379565730647631325052661587) * 10 ^ 70 +
        7559230240703222174298430776792923091012593504855872257078274615425246) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_143_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_144_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (144 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_144 :
    recurrence2Scalar3Main.coeff 144 =
      -(((3800063621430680239714578778807531873 * 10 ^ 70 +
        7315198710642097850470804690703233055063598548645712759594462769438694) * 10 ^ 70 +
        3410426669254489029522082554395243616433297619942213584381608273866535) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 17 = 15 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_144_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_145_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (145 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_145 :
    recurrence2Scalar3Main.coeff 145 =
      (((2075785758183613758633885415980416156 * 10 ^ 70 +
        9137235343590942094750302506575251432747683362368396821955129071833885) * 10 ^ 70 +
        1175037524532429354437148397655569567511959557906946927004729800441293) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 18 = 15 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_145_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_146_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (146 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_146 :
    recurrence2Scalar3Main.coeff 146 =
      (((58710937749162221336575768929824171526 * 10 ^ 70 +
        9591680592178405701000947549620492199907985097163582814188806819910485) * 10 ^ 70 +
        9235014762457943796909611523319512250548473810803679440748769921318844) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 19 = 15 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_146_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_147_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (147 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_147 :
    recurrence2Scalar3Main.coeff 147 =
      -(((323926851351975948862332959868877775758 * 10 ^ 70 +
        8027358755070586253664558360060104408682281965570870042956039906632868) * 10 ^ 70 +
        0521254808946584800448890774632473443084166999643715103490689261865314) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 20 = 15 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_147_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_148_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (148 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_148 :
    recurrence2Scalar3Main.coeff 148 =
      (((620098432630129240760806430739994184912 * 10 ^ 70 +
        5114449275484121776114377441299813636141173722447712418438808762489942) * 10 ^ 70 +
        4207378042768156155969101976102245211662514389160075770266439272877625) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 21 = 15 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_148_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_149_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (149 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_149 :
    recurrence2Scalar3Main.coeff 149 =
      (((1827847095415756363138268611395303836742 * 10 ^ 70 +
        1139062846825441703421103226267619715683401305980621479492797209311816) * 10 ^ 70 +
        8349651722824097814526254431506710400929734558179862553604102193230747) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 22 = 15 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_149_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_150_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (150 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_150 :
    recurrence2Scalar3Main.coeff 150 =
      -(((16028903813814848912093019525728676174920 * 10 ^ 70 +
        8565032261849144965698328652596235520229030316046780901842012577929010) * 10 ^ 70 +
        9483415364860025489113378079954506740985351216164886603459184977728982) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 23 = 15 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_150_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (151 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_151 :
    recurrence2Scalar3Main.coeff 151 =
      (((42093130024462253966396334484878045946249 * 10 ^ 70 +
        8522147419233704678333322456313774192742036014408606939508071973700557) * 10 ^ 70 +
        9190034567150406962162065563451217399689653698737816528027372238805628) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 24 = 15 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (152 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_152 :
    recurrence2Scalar3Main.coeff 152 =
      (((31155902323561879166588726801992628309973 * 10 ^ 70 +
        5859933665711478086349533498334934182465017153177548420893726147263941) * 10 ^ 70 +
        5132287319139431603136909950436291581845910118960126699624399654417125) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 25 = 15 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (153 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_153 :
    recurrence2Scalar3Main.coeff 153 =
      -(((626346134245919073862412718408090364684590 * 10 ^ 70 +
        1073641627632721100074008098672630793873010795657667366853563152560197) * 10 ^ 70 +
        1936863641021630409459917505491410637413798767312532761320778647472103) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 26 = 15 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (154 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_154 :
    recurrence2Scalar3Main.coeff 154 =
      (((2021365242858217329613662209713478251613971 * 10 ^ 70 +
        8451964765081169377509112632476821089378602329604871189879798111051828) * 10 ^ 70 +
        1111633806080650274658261429507323456801148635277753898188186432591793) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 27 = 15 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (155 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_155 :
    recurrence2Scalar3Main.coeff 155 =
      -(((466867460138513294080647170806320166574387 * 10 ^ 70 +
        8265045114787587226998616445428811838030541643838001750223904439391443) * 10 ^ 70 +
        4792058459539226567531684871126054160341911639595962410525420179124232) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 28 = 15 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (156 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_156 :
    recurrence2Scalar3Main.coeff 156 =
      -(((20384511314122723217915829756383538015750427 * 10 ^ 70 +
        4551852486737883298757008088380429997629606922273874446578449563167865) * 10 ^ 70 +
        6637616111710634383053036684047578007637102104269285455951990708989007) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 29 = 15 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (157 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_157 :
    recurrence2Scalar3Main.coeff 157 =
      (((77006005024165561009242362760480695769232779 * 10 ^ 70 +
        8667095747459296252803707707653605700044259230668063088369396506638230) * 10 ^ 70 +
        5502348156229684359865386147105761705592377822663750005690941779120046) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 30 = 15 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (158 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_158 :
    recurrence2Scalar3Main.coeff 158 =
      -(((52140371786254635752314467262647103519195092 * 10 ^ 70 +
        6246011103750974053808243272228861948948268622104187558922030899588002) * 10 ^ 70 +
        5937947197021381798757002329485207625257766340992622429482859163507089) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 31 = 15 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (159 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_159 :
    recurrence2Scalar3Main.coeff 159 =
      -(((623487910897617841552067200953201715807407266 * 10 ^ 70 +
        9189074984967884107386841521894807331469891857978569019864408478295402) * 10 ^ 70 +
        7198576992371261792691395111907804895677199244729871289805562725329656) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 32 = 15 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (160 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_160 :
    recurrence2Scalar3Main.coeff 160 =
      (((2622674053308970856040366943252435638934121098 * 10 ^ 70 +
        2385515920281665914853508812940256440723126408774775569247683463761958) * 10 ^ 70 +
        1340696732676770639226293018588241924453156106796845616607633936406129) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 33 = 15 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (161 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_161 :
    recurrence2Scalar3Main.coeff 161 =
      -(((2169616168288012802174581716478738014680242103 * 10 ^ 70 +
        1957206329809454184252652410548030861040278770147770734360732627561027) * 10 ^ 70 +
        9112295516456625540146105811765112834114826983846964982406695960829640) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 34 = 15 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (162 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_162 :
    recurrence2Scalar3Main.coeff 162 =
      -(((20788345887391282642976567057754539428300018514 * 10 ^ 70 +
        7751700266140420569817951672957673415791428189346897965443385661317194) * 10 ^ 70 +
        0819109726152223012551297749095592713272777036052032102161617663570541) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 35 = 15 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (163 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_163 :
    recurrence2Scalar3Main.coeff 163 =
      (((95198755141560674141963367117689625523516111155 * 10 ^ 70 +
        1139384895790821223039681084546338844561590810855271724302015399449679) * 10 ^ 70 +
        8924356602615153387565702444070565997451754835194056929355854507824080) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 36 = 15 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (164 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_164 :
    recurrence2Scalar3Main.coeff 164 =
      -(((108037713737241653665098640286763166593632734974 * 10 ^ 70 +
        4298380206073111456409342745544996989443642450523962641360862320313637) * 10 ^ 70 +
        0857020927911759759287102693650052378765509161013996487976283896800411) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 37 = 15 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (165 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_165 :
    recurrence2Scalar3Main.coeff 165 =
      -(((656196011045536059976450592097276762740054135105 * 10 ^ 70 +
        7595087660405195078034491642738585993766934041276061976558895424195859) * 10 ^ 70 +
        3115003067827365439686638197191726637828129078507804875099935157466462) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 38 = 15 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (166 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_166 :
    recurrence2Scalar3Main.coeff 166 =
      (((3620019065607129036962741302621935897792194524503 * 10 ^ 70 +
        2214103071095799128747580442145106359256245353483510050843814680827752) * 10 ^ 70 +
        2361718376948472023095990603356596413398550079744675735544207769462771) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 39 = 15 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (167 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_167 :
    recurrence2Scalar3Main.coeff 167 =
      -(((6624186303711728732212275751968027211265582044037 * 10 ^ 70 +
        6217399416645983959456426667698182209884330369427609693432366426343466) * 10 ^ 70 +
        2074765044612298930587835478158585072905526622115985167000585820862954) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 40 = 15 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (168 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_168 :
    recurrence2Scalar3Main.coeff 168 =
      -(((12824517184691660280849859561142337338837003771625 * 10 ^ 70 +
        9585299859704980540688002234657171880349357669721078742530622418248635) * 10 ^ 70 +
        1763941857088662506820128157099202663529426550164930127813098420474620) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 41 = 15 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (169 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_169 :
    recurrence2Scalar3Main.coeff 169 =
      (((117475725449067778655000822031355172476357674201927 * 10 ^ 70 +
        1092607555301376455611649124101857800865856836140215365354608366386982) * 10 ^ 70 +
        0966686392110633721143120358151976109545204537938443760264596148468419) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 42 = 15 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (170 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_170 :
    recurrence2Scalar3Main.coeff 170 =
      -(((324624036413727647721103078544435999498327576821930 * 10 ^ 70 +
        7500092954223616389669578456093635673485778465815141326337190579364500) * 10 ^ 70 +
        3810711981175240114306672165784797920675583119116987189279570835141660) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 43 = 15 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (171 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_171 :
    recurrence2Scalar3Main.coeff 171 =
      (((105720314695561731024157053911811822029240212910999 * 10 ^ 70 +
        7174507450102430272629454984334471940709359751526531149494705297848114) * 10 ^ 70 +
        1347050465554633625501931121264839686538961941866254258248316436343041) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 44 = 15 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (172 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_172 :
    recurrence2Scalar3Main.coeff 172 =
      (((2676642613153712837414575867047189828342474586760515 * 10 ^ 70 +
        1759747835295855901117936522462036257920684704176595016434459817782580) * 10 ^ 70 +
        1614325766484407539390748812533250375035234573268426041300499882197298) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 45 = 15 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (173 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_173 :
    recurrence2Scalar3Main.coeff 173 =
      -(((11233798566024202579456157032640825851243627578135744 * 10 ^ 70 +
        3295023587778605519624509169961637296146862127775936430473975389927864) * 10 ^ 70 +
        0776413054743378211413223565659739289584563575481495794360618372765125) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 46 = 15 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (174 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_174 :
    recurrence2Scalar3Main.coeff 174 =
      (((18661290051481535262743539295206806707673994492117647 * 10 ^ 70 +
        1297077754168022124200506087847822801209234116431885519425969750170047) * 10 ^ 70 +
        1293005080851361804135248672354556219513320831759783391555097624671156) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 47 = 15 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (175 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_175 :
    recurrence2Scalar3Main.coeff 175 =
      (((28453697598929416458665535450712861704034119503534313 * 10 ^ 70 +
        6297490025611086034590869675083447077907073983685079458786400972504402) * 10 ^ 70 +
        0734562827957627524517230473260462996251292787722780813376319007251382) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 48 = 15 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (176 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_176 :
    recurrence2Scalar3Main.coeff 176 =
      -(((269644916056950727320742910198692481387446263062309303 * 10 ^ 70 +
        0407162238798962675143453513856161520763767427072420724610314350955012) * 10 ^ 70 +
        4264860536838800627708475954947210604012082214367665165407901732350031) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 49 = 15 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (177 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_177 :
    recurrence2Scalar3Main.coeff 177 =
      (((777005840037157884923088569682186939665470105166206852 * 10 ^ 70 +
        5101883323078277839085403140011623812361760355364286028712280516194338) * 10 ^ 70 +
        5794587037555428162263723228248387461948223620029848270456307010779357) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 50 = 15 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (178 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_178 :
    recurrence2Scalar3Main.coeff 178 =
      -(((675144027943994330173024991469090453961928212389346264 * 10 ^ 70 +
        5440800338283662161430442229073775411111876173833301205595691195943338) * 10 ^ 70 +
        4399081153543126045359699099111424963693875417443312836899441834585212) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (179 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_179 :
    recurrence2Scalar3Main.coeff 179 =
      -(((3861163034700429878423062189586748245499432406405479077 * 10 ^ 70 +
        2093984432578550791576793023951955116945894988649274674554710334164509) * 10 ^ 70 +
        2563083709036260744100422109801117783119710133025779876448382395166611) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 52 = 15 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (180 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_180 :
    recurrence2Scalar3Main.coeff 180 =
      (((20091187815133324059360823004104370479394935838046441612 * 10 ^ 70 +
        1344598664152211073557480363628643968004602346205930152152760581621509) * 10 ^ 70 +
        1983789461077733005780773709364690098426152234717976395453474728613741) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 53 = 15 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (181 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_181 :
    recurrence2Scalar3Main.coeff 181 =
      -(((45183786026659436427081474112862166213245165858313659692 * 10 ^ 70 +
        0412353725675379459913235033611308322783834725348718435362858369082457) * 10 ^ 70 +
        2557261004860104902639092577366642547451580746226102698884009263743816) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 54 = 15 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (182 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_182 :
    recurrence2Scalar3Main.coeff 182 =
      (((12978259246160078033593743843587508520664860644271628563 * 10 ^ 70 +
        1340067907487255606253908381551560826138869616466656304543777739382515) * 10 ^ 70 +
        9025001165259789316381163999930117337319741539797642809861711975082675) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 55 = 15 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (183 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_183 :
    recurrence2Scalar3Main.coeff 183 =
      (((301846316629198700747596594764516633495214386537217537416 * 10 ^ 70 +
        6506814083778171613663796063828658770966027205609825736658304710622987) * 10 ^ 70 +
        5465611033611994091806384340831883731330848855205412151371237644925652) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 56 = 15 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (184 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_184 :
    recurrence2Scalar3Main.coeff 184 =
      -(((1250977696902708446286072791373296150842194877922726004710 * 10 ^ 70 +
        6234698233223007421655815472322829131176988998455529324969191996025824) * 10 ^ 70 +
        7086601215769106425669924577556625246572549261105349378743065099391433) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 57 = 15 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (185 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_185 :
    recurrence2Scalar3Main.coeff 185 =
      (((2512160189630570368654721704159366159332510159310412692852 * 10 ^ 70 +
        3603420778121636925602459384885972988871865444524989205208159731135102) * 10 ^ 70 +
        9072535231388703337367862454749936096267753976674239711599648107204421) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 58 = 15 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (186 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_186 :
    recurrence2Scalar3Main.coeff 186 =
      -(((373570193514700442555636286380849826525447891821915441273 * 10 ^ 70 +
        4596662641368696612218675651839952768838344597642626827997272288984275) * 10 ^ 70 +
        8348844664715124525109811202271975947786892978363795803248316994804124) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 59 = 15 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (187 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_187 :
    recurrence2Scalar3Main.coeff 187 =
      -(((16798354631833669072124888945368218349514598376743376016777 * 10 ^ 70 +
        0386051908051530369650672034423951515790509348411779404532631875059430) * 10 ^ 70 +
        3806173950880359269452830635508189569705407378742812763089894515244098) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 60 = 15 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (188 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_188 :
    recurrence2Scalar3Main.coeff 188 =
      (((67076836583370618777443061257268228597229605264739959906748 * 10 ^ 70 +
        3849198176040826412427554444284215075903623086955145354444457261982285) * 10 ^ 70 +
        1934380784259057822495216819065659514756694950025568619019606298726609) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 61 = 15 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (189 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_189 :
    recurrence2Scalar3Main.coeff 189 =
      -(((139826287769266632616288799394781309316890901821984554083723 * 10 ^ 70 +
        4725049169528630307471185223035130695427491932239774192797714139632076) * 10 ^ 70 +
        6725715067556203839356265147607258336167046279075352750667653934934472) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 62 = 15 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (190 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_190 :
    recurrence2Scalar3Main.coeff 190 =
      (((75957469240409178580776775392698719132635492073991671701503 * 10 ^ 70 +
        8979571627133718418809237614050261755514871356823432228646757793440415) * 10 ^ 70 +
        7366923943045723897752563243722066580375520310353779038685018986618075) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 63 = 15 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (191 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_191 :
    recurrence2Scalar3Main.coeff 191 =
      (((651189022506494288630058012942151837922777553264360969206814 * 10 ^ 70 +
        7451545496406432576445095306764843606135077680665414942461644840512089) * 10 ^ 70 +
        5257972154241405516068499084572530920409194735401965103198510130691483) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 64 = 15 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (192 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_192 :
    recurrence2Scalar3Main.coeff 192 =
      -(((3003210161840119728712963600377263213500596299857648836527159 * 10 ^ 70 +
        1211373378738377830581626360153320202328077227009672605549073747428825) * 10 ^ 70 +
        3977447757428099110890441282452892848018531054364708655808653831102934) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 65 = 15 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (193 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_193 :
    recurrence2Scalar3Main.coeff 193 =
      (((7301992695299001316703198460388135553728618067195985799562513 * 10 ^ 70 +
        0923375329033568322111373585460811405303856748945393017143988407199519) * 10 ^ 70 +
        9719720847914541167773117170490304349622382840458711678655868405761836) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 66 = 15 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (194 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_194 :
    recurrence2Scalar3Main.coeff 194 =
      -(((8887753612172579844192206622439442562716040712792633202792009 * 10 ^ 70 +
        5754295382824216713221790330129362084086532462821554060548166714214593) * 10 ^ 70 +
        5088201932695442031278667732436668012407000456497403798932464651012920) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 67 = 15 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (195 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_195 :
    recurrence2Scalar3Main.coeff 195 =
      -(((11591641582185166639212682747198104829491151555392082000096696 * 10 ^ 70 +
        6366258197451839988638232187807276935969580210241009534783472318590397) * 10 ^ 70 +
        0795874395142639854117631454727254917983750089735774647095707528267232) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 68 = 15 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (196 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_196 :
    recurrence2Scalar3Main.coeff 196 =
      (((99206092870155315372884897110134496242921100085793996961950024 * 10 ^ 70 +
        8250441719822203775320629359800197101458397477105539048777913096151574) * 10 ^ 70 +
        4854892388013193344221761240807111603654314020156129629429298574921371) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 69 = 15 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (197 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_197 :
    recurrence2Scalar3Main.coeff 197 =
      -(((311410677690717600156058848577804928776213259612041147982577483 * 10 ^ 70 +
        1129484540105774180733311779460532210965008576570498260856313058180913) * 10 ^ 70 +
        5532591438967011213150935106755511018762389651695947701763756987368693) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 70 = 15 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (198 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_198 :
    recurrence2Scalar3Main.coeff 198 =
      (((609806307112725055764508266313380454289419165346132250576452711 * 10 ^ 70 +
        8431547783834317224867036218905750720914032631770149088908809932695855) * 10 ^ 70 +
        2857202705644962385418308973137701502686790084317834812546883926921150) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 71 = 15 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (199 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_199 :
    recurrence2Scalar3Main.coeff 199 =
      -(((535800684655971970880251889562175198145648379805451700585149354 * 10 ^ 70 +
        4847633880464052420920239337075032803145642018809226773020172889533463) * 10 ^ 70 +
        0766324981517307811306835730003775440451375803611308493347458779161128) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 72 = 15 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (200 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_200 :
    recurrence2Scalar3Main.coeff 200 =
      -(((1412376319287922859005866195418026463802134297559994360845690289 * 10 ^ 70 +
        6702499266747119024294834752106884748360959489899969066188189736667503) * 10 ^ 70 +
        3824825443883816867332626385428925781249640162104276352101572218086158) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 73 = 15 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (201 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_201 :
    recurrence2Scalar3Main.coeff 201 =
      (((8412766427181781192419757768110016704173268210229698567355426583 * 10 ^ 70 +
        8358134084752538500523723841790756535083425311241258726711686183416885) * 10 ^ 70 +
        0464076517246355682057749410121221784658763636065316030053891466678017) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 74 = 15 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (202 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_202 :
    recurrence2Scalar3Main.coeff 202 =
      -(((24563621546589636210340619763296186472806937750063609215628983659 * 10 ^ 70 +
        7802873343322735593582441241743893578114893898292830775683657310260483) * 10 ^ 70 +
        2236935916477594323926571749364034339066983178902205954323834696959154) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 75 = 15 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (203 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_203 :
    recurrence2Scalar3Main.coeff 203 =
      (((49140163239598231066095467579816833795287886343252463847537448553 * 10 ^ 70 +
        7215971202756440482768885821469647817209839330587594166598466694775433) * 10 ^ 70 +
        7700954410650130165666218059508570119357073930967807200552038010037262) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 76 = 15 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (204 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_204 :
    recurrence2Scalar3Main.coeff 204 =
      -(((59451399445788166318374032105653640574689948667694757586448701042 * 10 ^ 70 +
        1386350313138483799258672259334918803783690776016882523144174625237865) * 10 ^ 70 +
        6800940177874070218184543034974839363115512449264763636080066017101985) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 77 = 15 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (205 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_205 :
    recurrence2Scalar3Main.coeff 205 =
      -(((24680904611689541127869669128742400521775839701447965668661391674 * 10 ^ 70 +
        0090386696109506295423298246630013056779924660165358483272808230833300) * 10 ^ 70 +
        1687633381567491276574422266654133538651488662772659275661778879902370) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 78 = 15 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (206 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_206 :
    recurrence2Scalar3Main.coeff 206 =
      (((392624972731296863894755649336504866440576648426369397009197928264 * 10 ^ 70 +
        1254730427540361024241776076015405804034720718630033744394884899232989) * 10 ^ 70 +
        1621705987487290609049315872777768208382643643121599461208624235127642) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 79 = 15 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (207 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_207 :
    recurrence2Scalar3Main.coeff 207 =
      -(((1375949853357741385243612079790120920344041394934309769808389540643 * 10 ^ 70 +
        1295678807490611533532521383261491548833209054830151561469335505564127) * 10 ^ 70 +
        5255984306585488659864677333187588013405084366779961344805922021185901) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 80 = 15 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (208 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_208 :
    recurrence2Scalar3Main.coeff 208 =
      (((3353511793523122292422297762032460553032666408665548185029464430012 * 10 ^ 70 +
        6647880813157854903149617583830727514537154769165565346194903385935206) * 10 ^ 70 +
        2137803277582467222976805967497038161122682824549144917709284164018786) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 81 = 15 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (209 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_209 :
    recurrence2Scalar3Main.coeff 209 =
      -(((6290580096448221648006691690863659044451755658441921951209554460798 * 10 ^ 70 +
        2716341593353393580086146947575380110136616113901299645239685852221866) * 10 ^ 70 +
        6529837803732921143911427329399304913648740465842391870387883987993169) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 82 = 15 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (210 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_210 :
    recurrence2Scalar3Main.coeff 210 =
      (((8505155613703505605687895102924253274918079888809591382616641662054 * 10 ^ 70 +
        6173923109356633751284585716073681820004047412991774560379272776184030) * 10 ^ 70 +
        3112433822698076765054552803245237018457119949825727310413861543591009) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 83 = 15 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (211 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_211 :
    recurrence2Scalar3Main.coeff 211 =
      -(((4120250773636624739207700561864843205288879294983476734439404917669 * 10 ^ 70 +
        2069485656550505460074751700594722413325015639567872826232014520946302) * 10 ^ 70 +
        3263001955293239077422834171952495993765612556593476401412201099570427) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 84 = 15 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (212 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_212 :
    recurrence2Scalar3Main.coeff 212 =
      -(((21272775209916010224754638669298364884260534320862590433232450480440 * 10 ^ 70 +
        0659352692905283932031025795843985544521274897001946344851267265060375) * 10 ^ 70 +
        8759738613125900110819630741484453977234063114520584973147087723886133) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 85 = 15 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (213 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_213 :
    recurrence2Scalar3Main.coeff 213 =
      (((96685761833268677543338157579830254412976701680880725900923921804369 * 10 ^ 70 +
        8023256364342368573594289046541872749408311922591704675708192381113016) * 10 ^ 70 +
        2687347040830188764872353091265530442700903634452699875489120460487135) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 86 = 15 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (214 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_214 :
    recurrence2Scalar3Main.coeff 214 =
      -(((272199574867059547862476679753968284896426235113772475177685254307533 * 10 ^ 70 +
        4268243428746263365795700613708758865318318025367766728518346880326266) * 10 ^ 70 +
        2191481757447890722797988351435495353281178213093197908607026316600738) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 87 = 15 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (215 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_215 :
    recurrence2Scalar3Main.coeff 215 =
      (((622272929054969794757880616691328292277765672580580349201707580656540 * 10 ^ 70 +
        7790919492649185851613762432065405165605410546469740956804741381465793) * 10 ^ 70 +
        3126916032030874378525566006110915488065019099468536975290728728953770) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 88 = 15 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (216 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_216 :
    recurrence2Scalar3Main.coeff 216 =
      -(((1239424044250439921465155065205131343596820931390863740299833178325611 * 10 ^ 70 +
        7243859344115737616137846741595201903881140207639284031504057952368740) * 10 ^ 70 +
        5038465858993438421345447813968211329332799507027074831480497549155205) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 89 = 15 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (217 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_217 :
    recurrence2Scalar3Main.coeff 217 =
      (((2209055638905605829035835182814189467499675978627772236192274817155151 * 10 ^ 70 +
        5710976707090005717013411338464235686138303015290920155639712989206665) * 10 ^ 70 +
        9364911292860017021987690034467189819729408733846883556442831382435130) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 90 = 15 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (218 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_218 :
    recurrence2Scalar3Main.coeff 218 =
      -(((3555234612332340129737488842262415792662279571309839465262873305771929 * 10 ^ 70 +
        7172644202699035931028688373454880009467320289821710882655428221129514) * 10 ^ 70 +
        0791504530742875310636691113043254933702528447096313861378193148541245) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 91 = 15 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (219 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_219 :
    recurrence2Scalar3Main.coeff 219 =
      (((5150255047662665903014486178024037997316188740657384188118725165726420 * 10 ^ 70 +
        0908829650791281757531903241107536721368562091091133082921312985700530) * 10 ^ 70 +
        0327336910805564455189435081996182435624018322851050307102777304756261) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 92 = 15 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (220 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_220 :
    recurrence2Scalar3Main.coeff 220 =
      -(((6589768130051102449672589185444425462955025371359150378023598732248805 * 10 ^ 70 +
        7710861577099557968440961256000592410031828902942976252062180546928633) * 10 ^ 70 +
        1360542591837765183403720988107354543024320584605035199481549987437943) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 93 = 15 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (221 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_221 :
    recurrence2Scalar3Main.coeff 221 =
      (((7050684018068733805075220237962643214159136516383043664598259472498440 * 10 ^ 70 +
        0199630496862201640751742286412124188644862514232884426095484831157239) * 10 ^ 70 +
        2844505857207947465108720285569259939542243272868153120195686085273740) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 94 = 15 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (222 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_222 :
    recurrence2Scalar3Main.coeff 222 =
      -(((5168716470740956523977789324714793052712473849720989995267008078305442 * 10 ^ 70 +
        8483865653778379699941905907103305700358859592749627623416429597208295) * 10 ^ 70 +
        7211809276631209786482729246958773439099729812103563492329394461637641) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 95 = 15 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (223 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_223 :
    recurrence2Scalar3Main.coeff 223 =
      -(((1009366321362714398674228019377850865899534756407076904170064524803453 * 10 ^ 70 +
        6225990244442857277266049321370120355130353124967780666128976968848425) * 10 ^ 70 +
        1640807476637323546051002464980832429903502520294983785206404225549790) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 96 = 15 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (224 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_224 :
    recurrence2Scalar3Main.coeff 224 =
      ((((1 * 10 ^ 70 +
        3935613923709828595809058989882796589512350057975312403405397063677945) * 10 ^ 70 +
        9064951824285026484869195552214027518646350064783444839955090157824503) * 10 ^ 70 +
        7244091442752909411510761686856051884585323059334765562064639934749222) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 97 = 15 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (225 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_225 :
    recurrence2Scalar3Main.coeff 225 =
      -((((3 * 10 ^ 70 +
        6280793616482342619982377093767137729942985946320363685560788558528768) * 10 ^ 70 +
        2255429402928173134187094045493343318314748167655945380126523904514554) * 10 ^ 70 +
        7608022659989811649003831281178681423870145058581595913296758536058583) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 98 = 15 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (226 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_226 :
    recurrence2Scalar3Main.coeff 226 =
      ((((7 * 10 ^ 70 +
        0448127251408493313004704718527580006097174763148467075654451322011504) * 10 ^ 70 +
        9490805849943188824579189090793027979798224182206038402461854508198554) * 10 ^ 70 +
        6206538033778773008960617866212291019867875937215224978022002325417829) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 99 = 15 +
      84 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (227 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_227 :
    recurrence2Scalar3Main.coeff 227 =
      -((((11 * 10 ^ 70 +
        7923384545632506246753389521621235805525766740945645336921205130082413) * 10 ^ 70 +
        1477010978848874031073768552975741324948769997172268530328162587446721) * 10 ^ 70 +
        5258085228908404023254025884626481358632729736491729777808957172670013) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 100 = 15 +
      85 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (228 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_228 :
    recurrence2Scalar3Main.coeff 228 =
      ((((17 * 10 ^ 70 +
        8573153026499881298530328628112553466781967285265770488899833613568851) * 10 ^ 70 +
        5101034552946660147010233389673893267292149150473365773739406789870963) * 10 ^ 70 +
        0253737626349007364840539181114381021311249025081941418552686534211306) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 101 = 15 +
      86 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (229 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_229 :
    recurrence2Scalar3Main.coeff 229 =
      -((((25 * 10 ^ 70 +
        0061694452959635648594759998631490476832646679897418842292799789777135) * 10 ^ 70 +
        5842126487706038182970179196386609831119497601641173149966791601741789) * 10 ^ 70 +
        8414124541612182460767211588697406709743156516863656960131616073339809) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 102 = 15 +
      87 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (230 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_230 :
    recurrence2Scalar3Main.coeff 230 =
      ((((32 * 10 ^ 70 +
        7579882808971532453785511882872861950793142058288085418276081754239108) * 10 ^ 70 +
        0662527990397035315925614397046025594931783078822165962204850003433997) * 10 ^ 70 +
        7957689262465146163548229792860359601188729305949320483819010689084566) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 103 = 15 +
      88 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (231 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_231 :
    recurrence2Scalar3Main.coeff 231 =
      -((((40 * 10 ^ 70 +
        4048026507539076339296510733514585626264569191835547582938313996868118) * 10 ^ 70 +
        9667869012876786437742419754205229512420294608513350190143068351961363) * 10 ^ 70 +
        8383194373481905480640019005426371673822679849905514212187604358577235) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 104 = 15 +
      89 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (232 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_232 :
    recurrence2Scalar3Main.coeff 232 =
      ((((47 * 10 ^ 70 +
        0863513843709600032690730539501261145626646417193899676419008063675821) * 10 ^ 70 +
        6183681470188042563361350325933317872893838061813937830051980821313589) * 10 ^ 70 +
        4432540564513955784585260869339939136741233756576587068186687254647313) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 105 = 15 +
      90 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar3Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (233 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_233 :
    recurrence2Scalar3Main.coeff 233 =
      -((((51 * 10 ^ 70 +
        9130268859450496790779173341053864063559668681565128704216296897810501) * 10 ^ 70 +
        5461054375509823247347216566963964832872875624915445994419331304433288) * 10 ^ 70 +
        1610173706025507708330488092909610692914533065595523730428348312047620) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 0 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
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
    rw [show 106 = 15 +
      91 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
