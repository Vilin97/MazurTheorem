/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B1_coeff_0
  recurrence2B1_coeff_1
  recurrence2B1_coeff_2
  recurrence2B1_coeff_3
  recurrence2B1_coeff_4
  recurrence2B1_coeff_5
  recurrence2B1_coeff_6
  recurrence2B1_coeff_7
  recurrence2B1_coeff_8
  recurrence2B1_coeff_9
  recurrence2B1_coeff_10
  recurrence2B1_coeff_11
  recurrence2B1_coeff_12
  recurrence2B1_coeff_13
  recurrence2B1_coeff_14
  recurrence2B1_coeff_15
  recurrence2B1_coeff_16
  recurrence2B1_coeff_17
  recurrence2B1_coeff_18
  recurrence2B1_coeff_19
  recurrence2B1_coeff_20
  recurrence2B1_coeff_21
  recurrence2B1_coeff_22
  recurrence2B1_coeff_23
  recurrence2B1_coeff_24
  recurrence2B1_coeff_25
  recurrence2B1_coeff_26
  recurrence2B1_coeff_27
  recurrence2B1_coeff_28
  recurrence2B1_coeff_29
  recurrence2B1_coeff_30
  recurrence2B1_coeff_31
  recurrence2B1_coeff_32
  recurrence2B1_coeff_33
  recurrence2B1_coeff_34
  recurrence2B1_coeff_35
  recurrence2B1_coeff_36
  recurrence2B1_coeff_37
  recurrence2B1_coeff_38
  recurrence2B1_coeff_39
  recurrence2B1_coeff_40
  recurrence2B1_coeff_41
  recurrence2B1_coeff_42
  recurrence2B1_coeff_43
  recurrence2B1_coeff_44
  recurrence2B1_coeff_45
  recurrence2B1_coeff_46
  recurrence2B1_coeff_47
  recurrence2B1_coeff_48
  recurrence2B1_coeff_49
  recurrence2B1_coeff_50
  recurrence2B1_coeff_51
  recurrence2B1_coeff_52
  recurrence2B1_coeff_53
  recurrence2B1_coeff_54
  recurrence2B1_coeff_55
  recurrence2B1_coeff_56
  recurrence2B1_coeff_57
  recurrence2B1_coeff_58
  recurrence2B1_coeff_59
  recurrence2B1_coeff_60
  recurrence2B1_coeff_61
  recurrence2B1_coeff_62
  recurrence2B1_coeff_63
  recurrence2B1_coeff_64
  recurrence2B1_coeff_65
  recurrence2B1_coeff_66
  recurrence2B1_coeff_67
  recurrence2B1_coeff_68
  recurrence2B1_coeff_69
  recurrence2B1_coeff_70
  recurrence2B1_coeff_71
  recurrence2B1_coeff_72
  recurrence2B1_coeff_73
  recurrence2B1_coeff_74
  recurrence2B1_coeff_75
  recurrence2B1_coeff_76
  recurrence2B1_coeff_77
  recurrence2B1_coeff_78
  recurrence2B1_coeff_79
  recurrence2B1_coeff_80
  recurrence2B1_coeff_81
  recurrence2B1_coeff_82
  recurrence2B1_coeff_83
  recurrence2B1_coeff_84
  recurrence2B1_coeff_85
  recurrence2B1_coeff_86
  recurrence2B1_coeff_87
  recurrence2B1_coeff_88
  recurrence2B1_coeff_89
  recurrence2B1_coeff_90
  recurrence2B1_coeff_91
  recurrence2B1_coeff_92
  recurrence2B1_coeff_93
  recurrence2B1_coeff_94
  recurrence2B1_coeff_95
  recurrence2B1_coeff_96
  recurrence2B1_coeff_97
  recurrence2B1_coeff_98
  recurrence2B1_coeff_99
  recurrence2B1_coeff_100
  recurrence2B1_coeff_101
  recurrence2B1_coeff_102
  recurrence2B1_coeff_103
  recurrence2B1_coeff_104
  recurrence2B1_coeff_105
  recurrence2B1_coeff_106
  recurrence2B1_coeff_107
  recurrence2B1_coeff_108
  recurrence2B1_coeff_109
  recurrence2B1_coeff_110
  recurrence2B1_coeff_111
  recurrence2B1_coeff_112
  recurrence2B1_coeff_113
  recurrence2B1_coeff_114
  recurrence2B1_coeff_115
  recurrence2B1_coeff_116
  recurrence2B1_coeff_117
  recurrence2B1_coeff_118
  recurrence2B1_coeff_119
  recurrence2B1_coeff_120
  recurrence2B1_coeff_121
  recurrence2B1_coeff_122
  recurrence2B1_coeff_123
  recurrence2B1_coeff_124
  recurrence2B1_coeff_125
  recurrence2B1_coeff_126
  recurrence2B1_coeff_127
  recurrence2B1_coeff_128
  recurrence2B1_coeff_129
  recurrence2B1_coeff_130
  recurrence2B1_coeff_131
  recurrence2B1_coeff_132
  recurrence2B1_coeff_133
  recurrence2B1_coeff_134
  recurrence2B1_coeff_135
  recurrence2B1_coeff_136
  recurrence2B1_coeff_137
  recurrence2B1_coeff_138
  recurrence2B1_coeff_139
  recurrence2B1_coeff_140
  recurrence2B1_coeff_141
  recurrence2B1_coeff_142
  recurrence2B1_coeff_143
  recurrence2B1_coeff_144
  recurrence2B1_coeff_145
  recurrence2B1_coeff_146
  recurrence2B1_coeff_147
  recurrence2B1_coeff_148
  recurrence2B1_coeff_149
  recurrence2B1_coeff_150
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

theorem recurrence2Scalar1Main_coeff_0 :
    recurrence2Scalar1Main.coeff 0 =
      (0 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_1 :
    recurrence2Scalar1Main.coeff 1 =
      (0 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_2 :
    recurrence2Scalar1Main.coeff 2 =
      (-404480 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_3 :
    recurrence2Scalar1Main.coeff 3 =
      (-7348271328 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_4 :
    recurrence2Scalar1Main.coeff 4 =
      (27503329618720 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_5 :
    recurrence2Scalar1Main.coeff 5 =
      (538904871211337216 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_6 :
    recurrence2Scalar1Main.coeff 6 =
      (-296005742115410499016 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_7 :
    recurrence2Scalar1Main.coeff 7 =
      (1708202552210422463458008 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_8 :
    recurrence2Scalar1Main.coeff 8 =
      (-1025243188921851347644877096 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_9 :
    recurrence2Scalar1Main.coeff 9 =
      (1365451106918446934295896550140 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_10 :
    recurrence2Scalar1Main.coeff 10 =
      (-661840139115459282124790182357960 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_11 :
    recurrence2Scalar1Main.coeff 11 =
      (-60648465426694726364646443539838206 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_12 :
    recurrence2Scalar1Main.coeff 12 =
      (222826559137399597751455285522451469514 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_13 :
    recurrence2Scalar1Main.coeff 13 =
      (-161377741426687435966241388574604056602798 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_14 :
    recurrence2Scalar1Main.coeff 14 =
      (68671137490440094730676841776760187964848747 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_15 :
    recurrence2Scalar1Main.coeff 15 =
      (-21424633508222065040026149323869502664658304069 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_16 :
    recurrence2Scalar1Main.coeff 16 =
      (5072864742099636339743123904044248584016409919599 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_17 :
    recurrence2Scalar1Main.coeff 17 =
      (-934052118624257740092206118849360570344417851699105 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_18 :
    recurrence2Scalar1Main.coeff 18 =
      (135379422407535178404332361835089895577716006371104633 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_19 :
    recurrence2Scalar1Main.coeff 19 =
      (-15506300564302540802252214762873854131671967491900055764 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_20 :
    recurrence2Scalar1Main.coeff 20 =
      (1396019350994075881665134755901682861441575756760200550892 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_21 :
    recurrence2Scalar1Main.coeff 21 =
      (-96260319390396100006063937643843331388398051575850180997055 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_22 :
    recurrence2Scalar1Main.coeff 22 =
      (4701866091695443197454099641498692346662593918121691132976221 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_23 :
    recurrence2Scalar1Main.coeff 23 =
      (-112315147744846049777095088300482603335425044502457101968594789 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_24 :
    recurrence2Scalar1Main.coeff 24 =
      (-5392348049145314384686997890410462278900834525148867504511703832 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_25 :
    recurrence2Scalar1Main.coeff 25 =
      (833117414863121478375929309177168416131469189831147329134180879896 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_26 :
    recurrence2Scalar1Main.coeff 26 =
      (-56276018611075344787030528639539874377580979940513594692862033306993 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_27 :
    recurrence2Scalar1Main.coeff 27 =
      (2429882723784907340489488364573425269264039444919970312020728452962855 : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_28 :
    recurrence2Scalar1Main.coeff 28 =
      -((4 * 10 ^ 70 +
        9496465773818816777147103165738750401987465629787580880064130721901309) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_29 :
    recurrence2Scalar1Main.coeff 29 =
      -((239 * 10 ^ 70 +
        7984718649543281840431706707903077393276682523166533614421548827224573) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_30 :
    recurrence2Scalar1Main.coeff 30 =
      ((32574 * 10 ^ 70 +
        6579276448250686830231781295024322411467995596253242502467851361525671) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_31 :
    recurrence2Scalar1Main.coeff 31 =
      -((2066182 * 10 ^ 70 +
        9928643141770216725830770826538412462401806258729422114760252247524874) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_32 :
    recurrence2Scalar1Main.coeff 32 =
      ((93069002 * 10 ^ 70 +
        2596625238780606588642259157679673076580483812034123646117656845883919) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_33 :
    recurrence2Scalar1Main.coeff 33 =
      -((3267789411 * 10 ^ 70 +
        4117214080864099353511039214854394855072687091691285951910149809348465) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_34 :
    recurrence2Scalar1Main.coeff 34 =
      ((95989580213 * 10 ^ 70 +
        6704367900236852189459338342404439542204670447135177274398729260034533) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_35 :
    recurrence2Scalar1Main.coeff 35 =
      -((2650347667847 * 10 ^ 70 +
        4363517537362964151361988147257111119221767611152389626081098646389096) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_36 :
    recurrence2Scalar1Main.coeff 36 =
      ((77832862946232 * 10 ^ 70 +
        7417068631974196509983742946559945370651963717431840653679639336800276) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_37 :
    recurrence2Scalar1Main.coeff 37 =
      -((2343215353179504 * 10 ^ 70 +
        1343541607965179749237070876193935545280025633456127243725812014602631) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_38 :
    recurrence2Scalar1Main.coeff 38 =
      ((59524120772250411 * 10 ^ 70 +
        4887121068060794630872692365678055317788819669232270992778401804175946) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_39 :
    recurrence2Scalar1Main.coeff 39 =
      -((948059817801156898 * 10 ^ 70 +
        9501904236042326817358309685902817437973108188017265946548626667206815) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_40 :
    recurrence2Scalar1Main.coeff 40 =
      -((2552186954070680897 * 10 ^ 70 +
        4286175996513293029626038691455261670453913804876350340762214010241343) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_41 :
    recurrence2Scalar1Main.coeff 41 =
      ((695430214858881129297 * 10 ^ 70 +
        0714122320962420878876811020612541349022952881943627085897743067703635) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_42 :
    recurrence2Scalar1Main.coeff 42 =
      -((23419380155485433182531 * 10 ^ 70 +
        2503947477078998438663450595710498197846702406202783433536011580012493) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_43 :
    recurrence2Scalar1Main.coeff 43 =
      ((464670242570584806694477 * 10 ^ 70 +
        6158566439523202601978197104795750987289907700628144823221866769946886) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_44 :
    recurrence2Scalar1Main.coeff 44 =
      -((6300844871831645099887089 * 10 ^ 70 +
        4023566743909061528534908388124781026440054146576304197434342207337241) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_45 :
    recurrence2Scalar1Main.coeff 45 =
      ((88054799003419434541631224 * 10 ^ 70 +
        3900123982173823651791334773217235733094270038502649455199491804815619) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_46 :
    recurrence2Scalar1Main.coeff 46 =
      -((2691464803067863149931941531 * 10 ^ 70 +
        8423329037407446935435646626640803805409701156737772821608520664618221) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_47 :
    recurrence2Scalar1Main.coeff 47 =
      ((98868615440425352767919467385 * 10 ^ 70 +
        6510853723080090769914159049722164380893815353034021255682189599603985) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_48 :
    recurrence2Scalar1Main.coeff 48 =
      -((2792095737168049920992795187693 * 10 ^ 70 +
        0384660404432817466810874308573895686015420915440852381294492783171294) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_49 :
    recurrence2Scalar1Main.coeff 49 =
      ((60970287206435439787376454130222 * 10 ^ 70 +
        8104293824427032578746618341030751544722208467306381039693460502436296) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_50 :
    recurrence2Scalar1Main.coeff 50 =
      -((1095898766205144908119734651348016 * 10 ^ 70 +
        8427304923325742441115579812833979130255501214273090181808488212604333) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_51 :
    recurrence2Scalar1Main.coeff 51 =
      ((16701132505900644405956119721706941 * 10 ^ 70 +
        9026828776451916985226009692032777511396178226063851908440528631794428) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_52 :
    recurrence2Scalar1Main.coeff 52 =
      -((185792198217506512647000125855689807 * 10 ^ 70 +
        9828826233062524206909930431042911054620909141253929205760279627376500) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_53 :
    recurrence2Scalar1Main.coeff 53 =
      -((532648834361887448162952525846528439 * 10 ^ 70 +
        4009397681313590589038286826209870579203854993630744794914182247041680) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_54 :
    recurrence2Scalar1Main.coeff 54 =
      ((124226680586890560221362090754954110420 * 10 ^ 70 +
        1226824552694873181525837178623251855277747113017518090550565842031985) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_55 :
    recurrence2Scalar1Main.coeff 55 =
      -((5008628603416346363399313104715842809868 * 10 ^ 70 +
        1998308500077039539997292445452229272624603694853126194869898424717942) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_56 :
    recurrence2Scalar1Main.coeff 56 =
      ((143976398620895209947940638866607620117489 * 10 ^ 70 +
        0734637857239934386944639896837226433964703142614838897020707492735430) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_57 :
    recurrence2Scalar1Main.coeff 57 =
      -((3417759356268425598524790752537551923658110 * 10 ^ 70 +
        1447902304290072333908537361850020299007792150900088359539154518547567) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_58 :
    recurrence2Scalar1Main.coeff 58 =
      ((70848926596123942838280474886921236110545674 * 10 ^ 70 +
        9494092833770405242903004327110661719354197522571037936219599744635656) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_59 :
    recurrence2Scalar1Main.coeff 59 =
      -((1322778709174206268057257202980228696443158578 * 10 ^ 70 +
        9358359054833073790360433232373951443045218686050604115801062730457725) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_60 :
    recurrence2Scalar1Main.coeff 60 =
      ((22660709697092966518527839158828478654651007579 * 10 ^ 70 +
        8013314759036560213753880980410372318983761207342469298570703273882099) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_61 :
    recurrence2Scalar1Main.coeff 61 =
      -((359629113391084778861715201409383441003518377442 * 10 ^ 70 +
        2076760657464508704756370254662171625846952967779352044593515793182354) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_62 :
    recurrence2Scalar1Main.coeff 62 =
      ((5298519760321517447173800528159733324887340026084 * 10 ^ 70 +
        5205055178798587582929030079721702857310794468284268647550370534623371) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_63 :
    recurrence2Scalar1Main.coeff 63 =
      -((72176403775744670061346019032557865474485281049797 * 10 ^ 70 +
        9375544545085215644781271534284489391504351481799524184437196224669370) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_64 :
    recurrence2Scalar1Main.coeff 64 =
      ((900001489129288170066131942788182352606317634380067 * 10 ^ 70 +
        0399016707224666185080390412937027081850175808038087234892397395209460) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_65 :
    recurrence2Scalar1Main.coeff 65 =
      -((10086072119495610816201955012154962200116064944656783 * 10 ^ 70 +
        6572857186333802505782361165002577858170612832253832295397692081604025) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_66 :
    recurrence2Scalar1Main.coeff 66 =
      ((97860811228733046858863620203226036898236980114696959 * 10 ^ 70 +
        8030289863896854596308725172840979948220412445237966364639224236031849) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_67 :
    recurrence2Scalar1Main.coeff 67 =
      -((743655135514497580949540782058846005545994758703276631 * 10 ^ 70 +
        4029743608036365279531802516036974562101969709168367753993149560156992) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_68 :
    recurrence2Scalar1Main.coeff 68 =
      ((2594633835842055714197028199569958997829551893152822739 * 10 ^ 70 +
        2645576311216716347952955489848672141890894007623452370953792487463280) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_69 :
    recurrence2Scalar1Main.coeff 69 =
      ((47926469819311982078630379475983806053845686288724750369 * 10 ^ 70 +
        2722861656081119515004087852248540226935728246634529961423375469127729) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_70 :
    recurrence2Scalar1Main.coeff 70 =
      -((1429952894272029150101227091865038038192316505411441933224 * 10 ^ 70 +
        2579791382681927670397006026074993880242649769449141839999412172432725) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_71 :
    recurrence2Scalar1Main.coeff 71 =
      ((25042414023656400537496715762783001119091515753022753730277 * 10 ^ 70 +
        2798113552139974819055108802105172093627087821179811216821226971533505) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_72 :
    recurrence2Scalar1Main.coeff 72 =
      -((358117409025632293055897421022882221020052820153494627768194 * 10 ^ 70 +
        3962227974207287006295525675057782736752763714837072656792644109022175) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_73 :
    recurrence2Scalar1Main.coeff 73 =
      ((4529105763921921667403145270503419779007523860699585870791339 * 10 ^ 70 +
        2873387399782963736501805501124315148725220038941582986437188238886514) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_74 :
    recurrence2Scalar1Main.coeff 74 =
      -((52315961946842683782890281473071816197482863294799643737096109 * 10 ^ 70 +
        7412019718874967444026929345917169853229474765128098078895549548002368) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_75 :
    recurrence2Scalar1Main.coeff 75 =
      ((561071544179665125521262432460805147338211005232769314111231237 * 10 ^ 70 +
        2315236178485531711627171902099275187317115683852970851210427864576759) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_76 :
    recurrence2Scalar1Main.coeff 76 =
      -((5641138234403647416874283335759011704651422110177901282289692423 * 10 ^ 70 +
        3595580657492332379615873041003832650927678714091112526883834749288759) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_77 :
    recurrence2Scalar1Main.coeff 77 =
      ((53510784380351411584058042675456752990428369312089082345984584736 * 10 ^ 70 +
        1382890718283854349087660836004393753385983349213899476997373007494355) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_78 :
    recurrence2Scalar1Main.coeff 78 =
      -((481069585183334979900567072423333887047278673063500331809057169935 * 10 ^ 70 +
        0871910168448025277687928460903430771724132038888710398709239774986352) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_79 :
    recurrence2Scalar1Main.coeff 79 =
      ((4112796493553615662262923192518723940853126108213762762731628089772 * 10 ^ 70 +
        4393840682938271095743894889876622209321438357979514606231762758329879) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_80 :
    recurrence2Scalar1Main.coeff 80 =
      -((33523761606097133292085217086913138088999882077940758179304982839997 * 10 ^ 70 +
        6221420378787328599779277801187507192495069977499767489973449793791200) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_81 :
    recurrence2Scalar1Main.coeff 81 =
      ((261044163304667706425859677349703023187705445136244417236039089701008 * 10 ^ 70 +
        2876550957751473693838944411493339828724446966125678372436110951010704) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_82 :
    recurrence2Scalar1Main.coeff 82 =
      -((1944810592300583545306135957104472727549435164250704681542212777440127 * 10 ^ 70 +
        8062010046087725853588103367335529351052410056585655422727101800191964) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_83 :
    recurrence2Scalar1Main.coeff 83 =
      (((1 * 10 ^ 70 +
        3878759949605777002931215768881769934474336777404513554065549224938256) * 10 ^ 70 +
        3034000184276056497752357392325758290143425103584284946400322845647969) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_84 :
    recurrence2Scalar1Main.coeff 84 =
      -(((9 * 10 ^ 70 +
        4960550102132254384824658019434282775208275613380915510937480505574267) * 10 ^ 70 +
        4496780986316892615456553995509828227744998792014450868439822938386941) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_85 :
    recurrence2Scalar1Main.coeff 85 =
      (((62 * 10 ^ 70 +
        3452189834112498344824294281162958716749485959450616652541674175341990) * 10 ^ 70 +
        5561473837162202926431442946788513647846643945066864034062905471750766) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_86 :
    recurrence2Scalar1Main.coeff 86 =
      -(((393 * 10 ^ 70 +
        0393666532922090258312884085779814997181639373840525911874628094531079) * 10 ^ 70 +
        5724582889263391233384819085006797008334327316943800252934435542411298) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_87 :
    recurrence2Scalar1Main.coeff 87 =
      (((2380 * 10 ^ 70 +
        6808693995215384856285111189662462331257910196327611740287447918433565) * 10 ^ 70 +
        9869053108031793457856903955337689859785322416095799045428906146297836) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_88 :
    recurrence2Scalar1Main.coeff 88 =
      -(((13860 * 10 ^ 70 +
        8620543073106564486703725697885318969624107915578771563965135804119817) * 10 ^ 70 +
        3136916926442286575649313438688461237464007618430846012187270106532963) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_89 :
    recurrence2Scalar1Main.coeff 89 =
      (((77589 * 10 ^ 70 +
        0030874147902910264447256154281275540668922099486798547838947261439264) * 10 ^ 70 +
        9143546526333389472440519004089338972320482086399523289359418041451803) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_90 :
    recurrence2Scalar1Main.coeff 90 =
      -(((417556 * 10 ^ 70 +
        0319007535294007941415738964155240658313357915663116802107771935339282) * 10 ^ 70 +
        8459753598067074261212040007352160900723932885072519996135846832414351) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_91 :
    recurrence2Scalar1Main.coeff 91 =
      (((2159764 * 10 ^ 70 +
        4974053201254642808961679805238981978833929511118497200270998441844221) * 10 ^ 70 +
        3772823342236850435109220911182101915461017615042370178265028095273732) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_92 :
    recurrence2Scalar1Main.coeff 92 =
      -(((10731471 * 10 ^ 70 +
        1856810353665577160685631968543466694463253957773185317866778381432500) * 10 ^ 70 +
        6493654293431976582051626071599203213417404334639153413974491856293640) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_93 :
    recurrence2Scalar1Main.coeff 93 =
      (((51191822 * 10 ^ 70 +
        7166673637036075644816674261752030383044134915675895213753798907438448) * 10 ^ 70 +
        3544512652535867281322657752241477634915202481413974565290821544413237) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_94 :
    recurrence2Scalar1Main.coeff 94 =
      -(((234267087 * 10 ^ 70 +
        4604279687214216704789011459970790552105572081638343239363570995877236) * 10 ^ 70 +
        9315317978467044810633037049545868650244231762809639500398476268818064) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_95 :
    recurrence2Scalar1Main.coeff 95 =
      (((1027486095 * 10 ^ 70 +
        8918920795450915680346523572588735694943178697222094152243854406007098) * 10 ^ 70 +
        7423608865412439300373381869565060857877913036465034129074146697381166) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_96 :
    recurrence2Scalar1Main.coeff 96 =
      -(((4312519436 * 10 ^ 70 +
        6239196303075081988450281556458068186810766288191363259533803234526851) * 10 ^ 70 +
        8293128866238623934959298653582088507719237023277676410248422022598899) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_97 :
    recurrence2Scalar1Main.coeff 97 =
      (((17273577964 * 10 ^ 70 +
        7993220819682593672405558109419654319021680450334899647175953119901108) * 10 ^ 70 +
        8355759436549071956655540279100544538582177773990373921024922685271362) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_98 :
    recurrence2Scalar1Main.coeff 98 =
      -(((65703164707 * 10 ^ 70 +
        3416139851734796480838261734852187477430437885382885564726239196049334) * 10 ^ 70 +
        3206583015900689152507504078661503314847770359099912437218943867900260) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_99 :
    recurrence2Scalar1Main.coeff 99 =
      (((235339118097 * 10 ^ 70 +
        7852590937315181708953117276896949814396589744930025865628975474197765) * 10 ^ 70 +
        5442253007795224104264516631116887343128474275072376127402186080591259) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_100 :
    recurrence2Scalar1Main.coeff 100 =
      -(((782974613221 * 10 ^ 70 +
        5543151655984267129673722491708403505734783805028792566915387861154618) * 10 ^ 70 +
        4541684287585951412338596714721527402287989203607649293134623549448620) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_101 :
    recurrence2Scalar1Main.coeff 101 =
      (((2365163282073 * 10 ^ 70 +
        9324079229874143217428826286761138027953142167080153840654699548012863) * 10 ^ 70 +
        7668088391966239381592521271296416005451107878027056274849815683560394) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_102 :
    recurrence2Scalar1Main.coeff 102 =
      -(((6214167069956 * 10 ^ 70 +
        0728833635196998973824098998146874544948506869637127558796601354724910) * 10 ^ 70 +
        0748081686393795668279453029366620313035708151089099896089388898418792) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_103 :
    recurrence2Scalar1Main.coeff 103 =
      (((12700246272995 * 10 ^ 70 +
        1534025122411058120549363570349043170558372759056924403616567786485719) * 10 ^ 70 +
        8193128328980994882613317458095337026010241284983969134112593067316698) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_104 :
    recurrence2Scalar1Main.coeff 104 =
      -(((10271187149706 * 10 ^ 70 +
        4444573481185262517808436848298838706092804076408448139522541165384347) * 10 ^ 70 +
        9906056155151228388227595235725383496487044092943953126668718375934896) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_105 :
    recurrence2Scalar1Main.coeff 105 =
      -(((81784636265101 * 10 ^ 70 +
        6179275121540706910741528071201346406284886837921318473161942613023053) * 10 ^ 70 +
        2362693393989791128785970114970904093743252546979998087436372921091884) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_106 :
    recurrence2Scalar1Main.coeff 106 =
      (((684112569228406 * 10 ^ 70 +
        6946169941733797763068017188458203155840339143297899027161834811026210) * 10 ^ 70 +
        7089092962800033617498233702436612251516705507720285461379489354389182) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_107 :
    recurrence2Scalar1Main.coeff 107 =
      -(((3791815016744393 * 10 ^ 70 +
        9027874083333207977791536540952745637918250341648125036162610758210386) * 10 ^ 70 +
        1542815825246194341290225174779715090892490147537258485018171587136798) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_108 :
    recurrence2Scalar1Main.coeff 108 =
      (((18149189000545066 * 10 ^ 70 +
        6876173784555774379937764482156301321713175690971586610256075525448835) * 10 ^ 70 +
        0949104934343561910599284897537857959633689451967623741159161463680965) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_109 :
    recurrence2Scalar1Main.coeff 109 =
      -(((77430046986284092 * 10 ^ 70 +
        2483010261119047706207494522276091247162740455750549871593492202392277) * 10 ^ 70 +
        0261120181888529329511977899607841258196521697285938525597106854077161) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_110 :
    recurrence2Scalar1Main.coeff 110 =
      (((285381092585964195 * 10 ^ 70 +
        5745353418142751098427723275033906172547577925785961882960037569269538) * 10 ^ 70 +
        8619427471595475877283219827469465710771058076332795633166288819390846) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_111 :
    recurrence2Scalar1Main.coeff 111 =
      -(((843012619050101703 * 10 ^ 70 +
        5507143694233011828960381993517955580538651627782031450917760709007114) * 10 ^ 70 +
        0138694839253282500392698649114319089542498772375095007656722592993715) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_112 :
    recurrence2Scalar1Main.coeff 112 =
      (((1634923129271142020 * 10 ^ 70 +
        4692971512686304794145886429047894295611254303879923673080061614585386) * 10 ^ 70 +
        8357955778331405254286143033838997592550171036937874075003993407218500) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_113 :
    recurrence2Scalar1Main.coeff 113 =
      (((36958106278088612 * 10 ^ 70 +
        9382603166933851485033406079825488336135636129248499468004437071442056) * 10 ^ 70 +
        4005630148872088397280272306167780104119776054941725452916531705378172) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_114 :
    recurrence2Scalar1Main.coeff 114 =
      -(((13479486309068161321 * 10 ^ 70 +
        6289557536648142308924330846127253588570323428511191578084877762266216) * 10 ^ 70 +
        8415681934230598602781453194658577998013428763975758435791603961912098) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_115 :
    recurrence2Scalar1Main.coeff 115 =
      (((32696032444939579774 * 10 ^ 70 +
        1551834032966531849869068423561287293381438871296528646048674267555963) * 10 ^ 70 +
        7461966455383679153774120396589451513498689884791441237242082522605201) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_116 :
    recurrence2Scalar1Main.coeff 116 =
      (((176043765246138751468 * 10 ^ 70 +
        2097548467551396803140190668455859407337849761622880047938667031305903) * 10 ^ 70 +
        9359771604840230588107977683483715860864440579741883796171639118997679) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_117 :
    recurrence2Scalar1Main.coeff 117 =
      -(((1971590689037401119813 * 10 ^ 70 +
        8845692204218908561967889097009644645426084185159132753435574857704993) * 10 ^ 70 +
        4631716292040919133859064546373493250620622584375017645839599902501938) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_118 :
    recurrence2Scalar1Main.coeff 118 =
      (((9559080136386197342213 * 10 ^ 70 +
        7357501426448694565801770445695468876812738981599651438271896561649543) * 10 ^ 70 +
        7813254166081238683205172131534791009409424329274032770977072266548500) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_119 :
    recurrence2Scalar1Main.coeff 119 =
      -(((24978063997325642948342 * 10 ^ 70 +
        6480692540201057370871064692768481551863408891475588183720107496646151) * 10 ^ 70 +
        0720885531136317650875671551288539841358943926230443046246505677133063) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_120 :
    recurrence2Scalar1Main.coeff 120 =
      -(((13476334784227916333273 * 10 ^ 70 +
        6939459294120174620837733272399286612610468999696358137617935982130159) * 10 ^ 70 +
        7223418516921953562945899293677869516377701900531321859300224305531850) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_121 :
    recurrence2Scalar1Main.coeff 121 =
      (((539648987071252207580516 * 10 ^ 70 +
        1659825289990917721172634114512270788900248290021808102461935865499402) * 10 ^ 70 +
        9360184951174080546399646113534709372203905414080020600193817673093757) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_122 :
    recurrence2Scalar1Main.coeff 122 =
      -(((3272146996989407869989383 * 10 ^ 70 +
        0700217447175821010448940334604202741212670236704823670362677589318110) * 10 ^ 70 +
        5013729081855033299031620472212888655385382189269401905398171988757761) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_123 :
    recurrence2Scalar1Main.coeff 123 =
      (((11601705824115019753275959 * 10 ^ 70 +
        1729308221309642818938172121669116080127535477974321485356002077718078) * 10 ^ 70 +
        9751885817246970705651234920668516153380522474149941984671683295816513) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_124 :
    recurrence2Scalar1Main.coeff 124 =
      -(((16892830047939413030672339 * 10 ^ 70 +
        2155847732662765798630441217304934540569189670295134038981633128314992) * 10 ^ 70 +
        0542364905592854890668395371686413498241552888434562085898332643432929) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_125 :
    recurrence2Scalar1Main.coeff 125 =
      -(((90525459306829139401543563 * 10 ^ 70 +
        9109529101926874796042769762052198313884053533385687583782630097854467) * 10 ^ 70 +
        9165817143237552673993623638747255370371471091947896050145029159094516) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_126 :
    recurrence2Scalar1Main.coeff 126 =
      (((804646943845235836578615762 * 10 ^ 70 +
        0185065299022055345158732760446382368659775946888677307819318140862433) * 10 ^ 70 +
        1807288153785222098715004186781950234541427126558259423589689614197544) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_127 :
    recurrence2Scalar1Main.coeff 127 =
      -(((3170331576950677597861848094 * 10 ^ 70 +
        3276354473890321330337760065296197767937521917804602826589704572279925) * 10 ^ 70 +
        7806033702323266745653669136096475497611807122083758683730453579659630) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_128 :
    recurrence2Scalar1Main.coeff 128 =
      (((5744395883762065807813919700 * 10 ^ 70 +
        7571540965043626024404311115640392203363915440417574113445876517578338) * 10 ^ 70 +
        2180890391015636383295766120896928445408990791055322794796826483654754) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_129 :
    recurrence2Scalar1Main.coeff 129 =
      (((11039963888327238088018397412 * 10 ^ 70 +
        1162839953819632251498099430434147397966992070700456490762658232280671) * 10 ^ 70 +
        2736545162662905493711244397812036906687788509077603974997954917225762) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_130 :
    recurrence2Scalar1Main.coeff 130 =
      -(((116582918607836536405834183817 * 10 ^ 70 +
        9282579004830389885570220764297370060931635395307968440884048178246914) * 10 ^ 70 +
        6189418994491637307229489293178256083553190248567401022770530039724668) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_131 :
    recurrence2Scalar1Main.coeff 131 =
      (((416206874423288051483901303339 * 10 ^ 70 +
        5149246722841989221712114322628761226920522273361582348375229241854623) * 10 ^ 70 +
        1728083885435451360364496287072902876975175816421848081626602684339559) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_132 :
    recurrence2Scalar1Main.coeff 132 =
      -(((904082877353674543686837571511 * 10 ^ 70 +
        3058711848019071563033903686538895524441474222226342358178726893387734) * 10 ^ 70 +
        7789441769337962179231180694874212819845123583542785650808165819937947) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_133 :
    recurrence2Scalar1Main.coeff 133 =
      (((1849330295492066819513461760443 * 10 ^ 70 +
        2569341552383987618282369685216505853476540398688075831462586221086995) * 10 ^ 70 +
        4371744010637767698840284822139105176290677171204453176135867664242370) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_134 :
    recurrence2Scalar1Main.coeff 134 =
      -(((5949126831115369069666967829114 * 10 ^ 70 +
        7408747193976264298984552272866514558466492587421380085062540723063999) * 10 ^ 70 +
        5517251165108535855770806742551852235734437620137386980990483090904794) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_135 :
    recurrence2Scalar1Main.coeff 135 =
      (((4005954322203169196573587085004 * 10 ^ 70 +
        7727041760493830319920706888579957900262418437468042123632865558480549) * 10 ^ 70 +
        4950311534573460282741028393352118033513319478791236099804232882334575) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_136 :
    recurrence2Scalar1Main.coeff 136 =
      (((167223685638958151096032664278712 * 10 ^ 70 +
        4004316717239780458209024361606073917438461853536637427143888482794321) * 10 ^ 70 +
        6737973594729615260471592164804001009677818446674091002124284632777295) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_137 :
    recurrence2Scalar1Main.coeff 137 =
      -(((1216789077965758021165300266828345 * 10 ^ 70 +
        9543440941521708051727625250802762379263759212197092531612735535047756) * 10 ^ 70 +
        5741157387644601328102751411869379336491693943362035063874008491292621) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_138 :
    recurrence2Scalar1Main.coeff 138 =
      (((3688637869007011171291784547973441 * 10 ^ 70 +
        9367085169896697160733909020703880616463434931831768092965802034768411) * 10 ^ 70 +
        9168569455028637960302585327460152069057806707948839157692685704958237) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_139 :
    recurrence2Scalar1Main.coeff 139 =
      (((270097187605604057459603551127428 * 10 ^ 70 +
        7671186865570062387533232054485230285527412489060120696887073875275979) * 10 ^ 70 +
        2044991489071584350887854669229954076079892606248884882819136781698887) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_140 :
    recurrence2Scalar1Main.coeff 140 =
      -(((42962521717064744184471970526629704 * 10 ^ 70 +
        2970086415021705772462825463288272343481406657872591304907908626021579) * 10 ^ 70 +
        1618387387928014531435118700697657693620979439471450236718839598577544) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_141 :
    recurrence2Scalar1Main.coeff 141 =
      (((111629159922101474733107567060021922 * 10 ^ 70 +
        4270098453837492673901113430347139915269054659931980238041288731495272) * 10 ^ 70 +
        5683447221619276854213027117459347240483384284134272455925735501060886) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_142 :
    recurrence2Scalar1Main.coeff 142 =
      (((279433684704637464870835436373675670 * 10 ^ 70 +
        5386658397212666811714357280529255043842496326977320569302918004305770) * 10 ^ 70 +
        0558260027122298708899623986028871335645015646564566094829534341794290) : ℚ) := by
  unfold recurrence2Scalar1Main
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

theorem recurrence2Scalar1Main_coeff_143 :
    recurrence2Scalar1Main.coeff 143 =
      -(((2172403115252479048440668743656115240 * 10 ^ 70 +
        6854345939459646155989128393990975373455214492388547191763411355895643) * 10 ^ 70 +
        6499358093292569435390899645345106176737674980371089462715794758946399) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Main_coeff_144 :
    recurrence2Scalar1Main.coeff 144 =
      -(((52061468172623598749029768012547226 * 10 ^ 70 +
        0220891477179171919603136357313372055971240271236481234834397239639704) * 10 ^ 70 +
        9556667138060110968236703462992063884942188998887218513759259912269128) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Main_coeff_145 :
    recurrence2Scalar1Main.coeff 145 =
      (((46265950330538593681030765605334218429 * 10 ^ 70 +
        0379252062615447275403954844637289251986596101591850405163186620266867) * 10 ^ 70 +
        2927075521216846983176858612828573528342906877955795752660105115653018) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Main_coeff_146 :
    recurrence2Scalar1Main.coeff 146 =
      -(((194519717332058516348006694550742989425 * 10 ^ 70 +
        3168003669253456804814693094273892275040655966718105923221635767068905) * 10 ^ 70 +
        4116947405892565901093857848077036441322938731447975585735787914484677) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Main_coeff_147 :
    recurrence2Scalar1Main.coeff 147 =
      (((20528936966179073171598445347335683061 * 10 ^ 70 +
        4324814615342447914667146880406272496340548192037584876853830076307354) * 10 ^ 70 +
        6842079181721422445248667388103978976841563769879905776040251843920753) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Main_coeff_148 :
    recurrence2Scalar1Main.coeff 148 =
      (((3053657466589775881965922374712468229430 * 10 ^ 70 +
        7255295517125438093238980283165991268922372199920461905085929908651863) * 10 ^ 70 +
        9973148666299095063884454134995844400753847994346173048821985401431260) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Main_coeff_149 :
    recurrence2Scalar1Main.coeff 149 =
      -(((12799280656841234636625720167165481863349 * 10 ^ 70 +
        2030569730268318047711464707316863256601449611036009341028874508756674) * 10 ^ 70 +
        1022665530029978952631536461126624129732394913207968026190318861293350) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence2Scalar1Main_coeff_150 :
    recurrence2Scalar1Main.coeff 150 =
      (((6965198596987771507221429486441387910528 * 10 ^ 70 +
        9673802682819035643945010941257649818349481046627446675787999865695479) * 10 ^ 70 +
        7080709929682824070836818142531107502790750054507542345448511246022285) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_151_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (151 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_151 :
    recurrence2Scalar1Main.coeff 151 =
      (((151391492872235919044962281869157996303259 * 10 ^ 70 +
        0118464400924941510236739959530568489695339306314686819254575744509001) * 10 ^ 70 +
        5710256580139561560124052953166560405713172190130738054175071626867669) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_151_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_152_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (152 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_152 :
    recurrence2Scalar1Main.coeff 152 =
      -(((680881598398747340193801825265564569311580 * 10 ^ 70 +
        8689500674376875307918395429677936011832727663166490234192770720578059) * 10 ^ 70 +
        2907557870276556561756284360541904724863338418531023524634721796041856) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 25 = 23 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_152_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_153_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (153 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_153 :
    recurrence2Scalar1Main.coeff 153 =
      (((610106624906183192535729130066824619310620 * 10 ^ 70 +
        1142536235970873077706894338533922967682150629387306639637420240643811) * 10 ^ 70 +
        8766225981729621250861654298852307249519237743091610100001576002669422) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 26 = 23 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_153_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_154_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (154 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_154 :
    recurrence2Scalar1Main.coeff 154 =
      (((6461298735042580221388147636178609526243994 * 10 ^ 70 +
        1823914070232730133196736269649483127784233544145496502572666663208494) * 10 ^ 70 +
        4005582501138958191715652658085615540000345536354631767796462221420504) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 27 = 23 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_154_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_155_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (155 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_155 :
    recurrence2Scalar1Main.coeff 155 =
      -(((32057109161512211267880860158470997154857680 * 10 ^ 70 +
        9854959910511824707394309074410592716380514069134916322030757464578055) * 10 ^ 70 +
        4320202776143798948667031246006909976842283031824832274677134589946336) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 28 = 23 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_155_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (156 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_156 :
    recurrence2Scalar1Main.coeff 156 =
      (((40410751332417383306088611255581383782263330 * 10 ^ 70 +
        9811918877147443879018694133803800987901532203018902023307674096941037) * 10 ^ 70 +
        9006674347083825761735955079570252894184162716533650205165020910005863) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 29 = 23 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_156_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (157 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_157 :
    recurrence2Scalar1Main.coeff 157 =
      (((236299777750241645303862309752795605761560462 * 10 ^ 70 +
        6474845719827529330912019693588633300556991905202694927909916445760094) * 10 ^ 70 +
        2673404219272698587395041620113326162585218846698356135803469106726828) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 30 = 23 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_157_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (158 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_158 :
    recurrence2Scalar1Main.coeff 158 =
      -(((1347640255539764947946691698779225850866801894 * 10 ^ 70 +
        4572651915294032403306379477418153307794972859105881034761711658684706) * 10 ^ 70 +
        5925607380880674758900332812185069785533715996544683993573380065115253) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 31 = 23 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_158_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (159 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_159 :
    recurrence2Scalar1Main.coeff 159 =
      (((2179653922662608520778315096500915350057889456 * 10 ^ 70 +
        4950284567430017927668880953905763953185923722565308100496922541690027) * 10 ^ 70 +
        0918712493448324643256296005456452633228509247656511057010987765994080) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 32 = 23 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_159_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (160 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_160 :
    recurrence2Scalar1Main.coeff 160 =
      (((7543597192803764399063484686209209774716801258 * 10 ^ 70 +
        4844080024556631462777294608175484384978512625322685271825537929147651) * 10 ^ 70 +
        1962031499174315669844464295809255554617345394414394519660145786628824) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 33 = 23 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_160_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (161 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_161 :
    recurrence2Scalar1Main.coeff 161 =
      -(((52259668065325313881124228230598359699689398061 * 10 ^ 70 +
        6997675819770182780215232728997539560237382920819924113713423391122739) * 10 ^ 70 +
        3930650813782259039107571377980612032724837052135412670427931148046649) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 34 = 23 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (162 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_162 :
    recurrence2Scalar1Main.coeff 162 =
      (((105604672266143078746695134798957358107112744577 * 10 ^ 70 +
        1949790807626654688318098667867436570217860453510360245431976969828635) * 10 ^ 70 +
        1419405861001809949383122662094942266509750711217652078840283939375409) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 35 = 23 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (163 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_163 :
    recurrence2Scalar1Main.coeff 163 =
      (((197450152999801774511692288859108422715335482555 * 10 ^ 70 +
        6830784712336936650395533143406093240335075141596508784388268661412949) * 10 ^ 70 +
        4641723045972674012501537834361721702740965388138447194024752443452015) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 36 = 23 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (164 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_164 :
    recurrence2Scalar1Main.coeff 164 =
      -(((1899299245591878911801021492133396472091928706467 * 10 ^ 70 +
        9580254641458886943377044869287602426775451494122781933309758875708175) * 10 ^ 70 +
        4467911678717042931532193809739921353111688141946052974509824345454722) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 37 = 23 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (165 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_165 :
    recurrence2Scalar1Main.coeff 165 =
      (((4888835184961910833687173449837226217087349309504 * 10 ^ 70 +
        9626025075332291337806994412904988624339373348967783986639594034891898) * 10 ^ 70 +
        9784185589553288317883981882678361344420473732992531397797715007141669) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 38 = 23 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (166 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_166 :
    recurrence2Scalar1Main.coeff 166 =
      (((2315594149101257414919220163514494530334985564816 * 10 ^ 70 +
        7688661541367878898198962112086454084838847336306077118221110715373643) * 10 ^ 70 +
        8496950943546086478283992381322173295675311511867390357859457308973742) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 39 = 23 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (167 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_167 :
    recurrence2Scalar1Main.coeff 167 =
      -(((61093790645123425665359553910475023144954535720485 * 10 ^ 70 +
        1835670683611179078480037131641732108025795197881129347094953606710310) * 10 ^ 70 +
        0803814546809944739690079389707120327509792833828727909483425151072312) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 40 = 23 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (168 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_168 :
    recurrence2Scalar1Main.coeff 168 =
      (((207299104687642405243588143602790461373188802298521 * 10 ^ 70 +
        4488145114243280964897465061870433221562638811399590621046994797032236) * 10 ^ 70 +
        1531647540837404064819041870617683927797051691804550077276056757549481) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 41 = 23 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (169 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_169 :
    recurrence2Scalar1Main.coeff 169 =
      -(((156440486402784575164762570509014717003709468035747 * 10 ^ 70 +
        0315905530857593403225558037140754763510837568430363865836951373338292) * 10 ^ 70 +
        0415643237726015284632570374176100011316250395404384911283332961965451) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 42 = 23 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (170 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_170 :
    recurrence2Scalar1Main.coeff 170 =
      -(((1512775525845693157865526899211757271257533001485942 * 10 ^ 70 +
        6132063286804707369432402830657840113124969464579921093293241590390386) * 10 ^ 70 +
        3646248492656938109821925093958399831810236047861713953511462699416242) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 43 = 23 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (171 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_171 :
    recurrence2Scalar1Main.coeff 171 =
      (((7361653280122369814786670613817354068989131270570630 * 10 ^ 70 +
        6276689965701426388568801721895269824240730446354818103343909189150454) * 10 ^ 70 +
        1009622607415600713772378176778292819614747174040455659040871069242059) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 44 = 23 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (172 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_172 :
    recurrence2Scalar1Main.coeff 172 =
      -(((13432681598432238197546702599615906506717618475362366 * 10 ^ 70 +
        4380332053383636921674968968516702691160598208357135153466067905951733) * 10 ^ 70 +
        4568437569214117834651454073251106594084161829326498617551780996250442) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 45 = 23 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (173 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_173 :
    recurrence2Scalar1Main.coeff 173 =
      -(((19132004189532396160526515732308522121635640718838726 * 10 ^ 70 +
        2349700309839966753688182086633057813009535884098558814385452241849528) * 10 ^ 70 +
        4154303892298943775341524818892618896422542276407901105324408847235182) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 46 = 23 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (174 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_174 :
    recurrence2Scalar1Main.coeff 174 =
      (((199933415931712364657006698905184614190760136323406411 * 10 ^ 70 +
        4670585267948563952761164754945673955940672153352372359475538082787599) * 10 ^ 70 +
        4182122088919007742975389151561478035852808058543403929552407358550145) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 47 = 23 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (175 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_175 :
    recurrence2Scalar1Main.coeff 175 =
      -(((590264693082111170512776917691840075891950891784572877 * 10 ^ 70 +
        6588363023782066506215936882296572101950425697994991609493512078046722) * 10 ^ 70 +
        1736273383673102616106274507495115441323245966018601777795086357372705) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 48 = 23 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (176 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_176 :
    recurrence2Scalar1Main.coeff 176 =
      (((450268885834677150699332929463796122598413251627417051 * 10 ^ 70 +
        5857365059473078029299091307777618429552300376939333707936924062967530) * 10 ^ 70 +
        5854109521403605026340670468929899080544955889620709197743884489719185) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 49 = 23 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (177 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_177 :
    recurrence2Scalar1Main.coeff 177 =
      (((3530969930929979358488832973216346575749058081359314193 * 10 ^ 70 +
        2595847068076732929031756637154139975559271453935678809785129879028905) * 10 ^ 70 +
        8354338658661173165865726809346816127475077540141874861671126716516762) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 50 = 23 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (178 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_178 :
    recurrence2Scalar1Main.coeff 178 =
      -(((17470230401364356729209450458207917107825229258435049461 * 10 ^ 70 +
        5537064211807583066892101638362929465776870125427784341860954287585470) * 10 ^ 70 +
        2782373117251168406840667544872130117709391706715388293444786230781830) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (179 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_179 :
    recurrence2Scalar1Main.coeff 179 =
      (((36563816802827254906999330982289885296102554076321004946 * 10 ^ 70 +
        5303660717383220971686107336623436623843777583068230798904019101454936) * 10 ^ 70 +
        8017762500278147814507994902630317776022372282599389379609908446511128) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 52 = 23 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (180 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_180 :
    recurrence2Scalar1Main.coeff 180 =
      (((7707571802957994719435051300017745937072301931314703037 * 10 ^ 70 +
        5898744499671878067701612196509660815824204363794090796100983677469370) * 10 ^ 70 +
        4565173202330357441834703225473757635077160068567813402311621186474245) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 53 = 23 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (181 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_181 :
    recurrence2Scalar1Main.coeff 181 =
      -(((334220964268205646597320604136302406535350809016865175052 * 10 ^ 70 +
        7345050835429703450374587870091514054917393083250324433813673418410141) * 10 ^ 70 +
        2543407657281567517669950487633001181320839133785873172553000802816739) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 54 = 23 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (182 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_182 :
    recurrence2Scalar1Main.coeff 182 =
      (((1221201560455158147001143325682852828901844090458111097100 * 10 ^ 70 +
        1589839235019346043899461466742384752006611723833250383627134399136651) * 10 ^ 70 +
        9302373865877268113487880273959879630257188098689101974882464034826097) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 55 = 23 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (183 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_183 :
    recurrence2Scalar1Main.coeff 183 =
      -(((2002890835285665726725435305202621309061891690871252639559 * 10 ^ 70 +
        5362236631868135606267045133105257958144838397098264553045294260605608) * 10 ^ 70 +
        0096268998113666938905022026496559509173888227008994388753243354003210) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 56 = 23 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (184 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_184 :
    recurrence2Scalar1Main.coeff 184 =
      -(((1974994156265085183779973347090973305763176933330083030856 * 10 ^ 70 +
        6517699452688933862672483804848710211481314125059005968133606503501158) * 10 ^ 70 +
        4708438419540365093066215691882815820067469596721963907883808210123113) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 57 = 23 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (185 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_185 :
    recurrence2Scalar1Main.coeff 185 =
      (((23257505776859172624239483184925134815435431166742918560997 * 10 ^ 70 +
        9894982177117997711641065784749396578811039784537399485956729098033201) * 10 ^ 70 +
        6161587010034607135545771140233992570131419840843839390574889540586345) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 58 = 23 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (186 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_186 :
    recurrence2Scalar1Main.coeff 186 =
      -(((74694716289916314571613251812374150269874412478647340395054 * 10 ^ 70 +
        3558331449972055883687821034959143911810574272691953277864317041517139) * 10 ^ 70 +
        2557333217412198410892359087068259768811715736786694537589747001633164) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 59 = 23 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (187 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_187 :
    recurrence2Scalar1Main.coeff 187 =
      (((113396418938311067788793745302215873510992811881867582171934 * 10 ^ 70 +
        5394844961928314907777745227576214392017152047094105749785343803080944) * 10 ^ 70 +
        6492390194494011927258624105614985612309851899605205894665295682658281) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 60 = 23 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (188 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_188 :
    recurrence2Scalar1Main.coeff 188 =
      (((114925709998437481561798771392093603601548930099116095873158 * 10 ^ 70 +
        3448537090915833212654614416016444499875291304737423040226164790181319) * 10 ^ 70 +
        4881528962323426370058210565232532475238951514760432373651236859223493) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 61 = 23 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (189 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_189 :
    recurrence2Scalar1Main.coeff 189 =
      -(((1271332227879790434117688979781491845389767687864795832113354 * 10 ^ 70 +
        8863866487449068875484174564306468114645399983715357353104520479532923) * 10 ^ 70 +
        2249373519682362896078994895287889598069542988586085779956336883027902) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 62 = 23 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (190 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_190 :
    recurrence2Scalar1Main.coeff 190 =
      (((4104641454521958208791442700337213111815386120864490212889557 * 10 ^ 70 +
        5565295864169558778589378597558343490122024822846085941273806822707511) * 10 ^ 70 +
        1118531689137952129332783860297081217572690888549991948200092758525827) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 63 = 23 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (191 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_191 :
    recurrence2Scalar1Main.coeff 191 =
      -(((6976212076975427887890114637585236110350809709704136230189174 * 10 ^ 70 +
        0141147257215813320839666002238665080941241530994602865063115649227380) * 10 ^ 70 +
        3729828993435037535428711251357537994622463373258735792352433629791934) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 64 = 23 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (192 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_192 :
    recurrence2Scalar1Main.coeff 192 =
      -(((1290008678902408699807928666935869017621282370453522648324499 * 10 ^ 70 +
        8146056954052648787457138480625618175589487536350435332010497650482112) * 10 ^ 70 +
        3170497615730066098193969762271883768166439257391320829936502352666720) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 65 = 23 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (193 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_193 :
    recurrence2Scalar1Main.coeff 193 =
      (((52331809700451532853785635643015673308806664984473804458767938 * 10 ^ 70 +
        0645399183295902749313719537238792525563978927898769051394008547992931) * 10 ^ 70 +
        7799683099396825082693744163516695975117105876270444639127827860146208) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 66 = 23 +
      43 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (194 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_194 :
    recurrence2Scalar1Main.coeff 194 =
      -(((194510205053656625581384091102829502293749202598387331559555597 * 10 ^ 70 +
        2999333558987444040377846094823324593073034738925024841589986551232630) * 10 ^ 70 +
        3171150449309529684759218191838905027648521300551903773902515005088681) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 67 = 23 +
      44 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (195 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_195 :
    recurrence2Scalar1Main.coeff 195 =
      (((412645496293888699171064079314228157050111379446970066096457072 * 10 ^ 70 +
        8480008591313949157066663556641401144718985506954254157007018022601394) * 10 ^ 70 +
        4267406067494721858270824485297196333386653251092596264847651574428946) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 68 = 23 +
      45 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (196 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_196 :
    recurrence2Scalar1Main.coeff 196 =
      -(((352291647584392994161201735479366129156545422034131959886946959 * 10 ^ 70 +
        8877088682623850811712063955740580666530682707625101494329309913555265) * 10 ^ 70 +
        9367311442159688177674113225673360465177935695442157767216746496910135) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 69 = 23 +
      46 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (197 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_197 :
    recurrence2Scalar1Main.coeff 197 =
      -(((1235495839541026873859491390491464559317489154791864661779571736 * 10 ^ 70 +
        5914308030505865774311795898212906138228262062803076029688505004081851) * 10 ^ 70 +
        0326220445728312709579165149382538443864782558891883558690547432163789) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 70 = 23 +
      47 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (198 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_198 :
    recurrence2Scalar1Main.coeff 198 =
      (((6980233606135199643528056068897943017052630599586923836743743937 * 10 ^ 70 +
        2156335904611049987858720904508236032654850084267000704350387840720245) * 10 ^ 70 +
        8236736921342051823693357594304329526914638273992147757513415734883694) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 71 = 23 +
      48 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (199 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_199 :
    recurrence2Scalar1Main.coeff 199 =
      -(((19597068102068607155645316494256254721417454807874455082163650105 * 10 ^ 70 +
        0303704847485928157814262682476969674037049962788821680906108468669917) * 10 ^ 70 +
        0808054298725058701077206950942610965351470130650341781526716308383203) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 72 = 23 +
      49 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (200 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_200 :
    recurrence2Scalar1Main.coeff 200 =
      (((34457678637971689932419582195658117334108361084489203530740886180 * 10 ^ 70 +
        6156436935618790458059979527954996184784096103617090809356415369630205) * 10 ^ 70 +
        0909014125520685637613082328493157738991552359325638372613600331742129) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 73 = 23 +
      50 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (201 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_201 :
    recurrence2Scalar1Main.coeff 201 =
      -(((19092072046893101928308097897961861944408226060890920361659338482 * 10 ^ 70 +
        3451045366114291817265309299006206603616145412723844260546071066512114) * 10 ^ 70 +
        4076634264567409066119807288861938270802294681325987269077277906590087) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 74 = 23 +
      51 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (202 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_202 :
    recurrence2Scalar1Main.coeff 202 =
      -(((123634760017121994258548069885800418082026883665582503325171388206 * 10 ^ 70 +
        7284129718744735490776635312403285895556404542920150774962365517235784) * 10 ^ 70 +
        3505513616945979180381659307111355516843820886781482020370438567067957) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 75 = 23 +
      52 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (203 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_203 :
    recurrence2Scalar1Main.coeff 203 =
      (((586799587985841740430295681785035052643683948818067976227308214851 * 10 ^ 70 +
        5582276632302031170588000288979602542116022862964362478782784265044231) * 10 ^ 70 +
        1596892341854615994039655522916987204146865497764941445219423852456736) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 76 = 23 +
      53 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (204 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_204 :
    recurrence2Scalar1Main.coeff 204 =
      -(((1592032179392165290587256440133199242567332647529518064738689971579 * 10 ^ 70 +
        0539890895666167660318478575592444881211244712973809529619259454301400) * 10 ^ 70 +
        8951325125148779618073369389996528675743335943753920729266153075692746) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 77 = 23 +
      54 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (205 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_205 :
    recurrence2Scalar1Main.coeff 205 =
      (((2993379611455368361859822788624519116626410743612267893572816403691 * 10 ^ 70 +
        2869488049333552815475308366782187615924349778486944607059605580987520) * 10 ^ 70 +
        7904053570265466044357416892298242688471155162069294383680601195186393) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 78 = 23 +
      55 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (206 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_206 :
    recurrence2Scalar1Main.coeff 206 =
      -(((3153430352361727679235849747456110583433439022455882172528055573694 * 10 ^ 70 +
        7624397987224783463609325970765170550052164563551373325298449085682782) * 10 ^ 70 +
        7987457321344848109714399781111046966421179285602100198295929884541274) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 79 = 23 +
      56 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (207 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_207 :
    recurrence2Scalar1Main.coeff 207 =
      -(((3321422515512505423663068704403367001883630869037060760241548579641 * 10 ^ 70 +
        2770626323817987429989381257970318042920093665881895054232022719530069) * 10 ^ 70 +
        7477629944215181121050140755947112357893452284865560230130893708590465) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 80 = 23 +
      57 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (208 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_208 :
    recurrence2Scalar1Main.coeff 208 =
      (((28776031131713211046211456759592857857683832763855903638835065636387 * 10 ^ 70 +
        5409517958336141860696473625800724722017928778067824106859819485030005) * 10 ^ 70 +
        4063268282939476140121776224743098358706716752900689693520363629475815) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 81 = 23 +
      58 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (209 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_209 :
    recurrence2Scalar1Main.coeff 209 =
      -(((94267270901318899610835942642301734142864198292519309569087312560987 * 10 ^ 70 +
        3447188549030444424069741264560419434339659315523893590644174937092419) * 10 ^ 70 +
        3672837870949367282284934764028311104925922166894191134128433581632189) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 82 = 23 +
      59 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (210 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_210 :
    recurrence2Scalar1Main.coeff 210 =
      (((222637180527994681587190668029343983763226926998952500976757942618943 * 10 ^ 70 +
        1476937314127117537832940488285302595683324473488105739364148700129095) * 10 ^ 70 +
        4050304650813031850455058096666698330625753450862178629714816869154181) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 83 = 23 +
      60 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (211 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_211 :
    recurrence2Scalar1Main.coeff 211 =
      -(((407100185168065928236563046452389852866490092787886287345670213467780 * 10 ^ 70 +
        9478512329762640761992442859329659488007062927264065763164700269571073) * 10 ^ 70 +
        7643700709008724232564361400843439941201580904746865037768098485860329) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 84 = 23 +
      61 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (212 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_212 :
    recurrence2Scalar1Main.coeff 212 =
      (((528078252195714816471344691003330253356288978330429667435538175644407 * 10 ^ 70 +
        4953887390845987209717218462036305838520133399249556334518288124720497) * 10 ^ 70 +
        6586532711640458118180045842135802017147644681929260626907669822426445) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 85 = 23 +
      62 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (213 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_213 :
    recurrence2Scalar1Main.coeff 213 =
      -(((181166222123597029740641560782580511190094779143520223666701500624643 * 10 ^ 70 +
        2524220255764504539020101553780200598511885339059845607546721308616427) * 10 ^ 70 +
        8587907572730981742672644137085569583372254983822266402016146980344475) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 86 = 23 +
      63 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (214 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_214 :
    recurrence2Scalar1Main.coeff 214 =
      -(((1618516322792476896773901049503801310168195587660676019709435842949419 * 10 ^ 70 +
        0831608651720236719677776703397106420731118226402268889150876545531948) * 10 ^ 70 +
        8203332561399510793356975135123396803175395417274546985303297244101486) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 87 = 23 +
      64 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (215 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_215 :
    recurrence2Scalar1Main.coeff 215 =
      (((6858330933875202306519299223694481102390861961402932520076146401432044 * 10 ^ 70 +
        6588522776688872481940181329553973145969424339924714650003669182084987) * 10 ^ 70 +
        9096549070345969904058367321217948493854863993207197502663015066246083) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 88 = 23 +
      65 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (216 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_216 :
    recurrence2Scalar1Main.coeff 216 =
      -((((1 * 10 ^ 70 +
        8996759389885912229599450269956226308308631811532694065001761550562588) * 10 ^ 70 +
        8650769520523524740611147444315929248605605499220173903624759618661780) * 10 ^ 70 +
        0877339874847300201220533353023016735507699862863839040095817396849453) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 89 = 23 +
      66 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (217 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_217 :
    recurrence2Scalar1Main.coeff 217 =
      ((((4 * 10 ^ 70 +
        3251539883790307213667779079343593147471670792442157425722374092550303) * 10 ^ 70 +
        5626415322855040298479011591583759882267608636471980603107675821736234) * 10 ^ 70 +
        8003488779608812002230033699757309960031538987161567217367064813887249) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 90 = 23 +
      67 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (218 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_218 :
    recurrence2Scalar1Main.coeff 218 =
      -((((8 * 10 ^ 70 +
        6276325414366965722571654072813453365422766967386149902056427809298374) * 10 ^ 70 +
        7783700368282825922185337232857029127584691443709310640494394854818563) * 10 ^ 70 +
        3170403119424809943935190871009152711336219554016942962995901055605795) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 91 = 23 +
      68 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (219 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_219 :
    recurrence2Scalar1Main.coeff 219 =
      ((((15 * 10 ^ 70 +
        4585428244743827628583106701798993644836562368696596979779247669325571) * 10 ^ 70 +
        7392861378990737569219774013934270291487418508953398701598569913646425) * 10 ^ 70 +
        2604619237214130859179620772619134480248368512207584856327095378269670) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 92 = 23 +
      69 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (220 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_220 :
    recurrence2Scalar1Main.coeff 220 =
      -((((25 * 10 ^ 70 +
        0976259729552279913458568303528210405323802221589666655878309395015412) * 10 ^ 70 +
        5469492902544638257825551170373456204959727593210566555678315910906985) * 10 ^ 70 +
        1257532986419433231624774398958818676930718885436708250445121327169647) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 93 = 23 +
      70 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (221 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_221 :
    recurrence2Scalar1Main.coeff 221 =
      ((((36 * 10 ^ 70 +
        8338657384600994829466724155016610262145756685488116976153854218489894) * 10 ^ 70 +
        4320692645631063706188778350595646506816103120743759987606983107805485) * 10 ^ 70 +
        3874560841677717715248328636655684691376583764800452673152486627480099) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 94 = 23 +
      71 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (222 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_222 :
    recurrence2Scalar1Main.coeff 222 =
      -((((48 * 10 ^ 70 +
        0780917347272623406891882903554143135339559547000888019396677529983627) * 10 ^ 70 +
        1396267200764560809637557136122947928108453510778810200684690634237135) * 10 ^ 70 +
        2316317265826697373708841157016325051579804406024003555685572647191536) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 95 = 23 +
      72 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (223 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_223 :
    recurrence2Scalar1Main.coeff 223 =
      ((((53 * 10 ^ 70 +
        3018172311160924104274317624935278860733878980774527798141260773281655) * 10 ^ 70 +
        1764084759110118943978727774835032845041336095714053808724257127000954) * 10 ^ 70 +
        6554581505948743328433910630489657097759806239220846639829010146449208) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 96 = 23 +
      73 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (224 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_224 :
    recurrence2Scalar1Main.coeff 224 =
      -((((43 * 10 ^ 70 +
        0361270464652415241149404501694104320563154529378215911557222249166336) * 10 ^ 70 +
        0461562906957102812532386060943515303299427778262750947410969532743193) * 10 ^ 70 +
        6942213265982444091195879290571347323942337430905888043660692227285160) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 97 = 23 +
      74 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (225 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_225 :
    recurrence2Scalar1Main.coeff 225 =
      ((((3 * 10 ^ 70 +
        3072353631615462930331368487471974555147048653830315047223273705551794) * 10 ^ 70 +
        7206818089723514352863041615898078394483271029707503373017212838012239) * 10 ^ 70 +
        9193040353627386541240178383358201349312618584933990134450327323142192) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 98 = 23 +
      75 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (226 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_226 :
    recurrence2Scalar1Main.coeff 226 =
      ((((84 * 10 ^ 70 +
        0257390087905342719844770293941242679579581122847733486012217273151039) * 10 ^ 70 +
        6736795346513580275958821684750561420767915964259735476349445459783830) * 10 ^ 70 +
        7696856991885511768151192315279736055848298719681660356254148909067228) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 99 = 23 +
      76 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (227 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_227 :
    recurrence2Scalar1Main.coeff 227 =
      -((((239 * 10 ^ 70 +
        5977744778695279865405524581373651818382916525237047721833009120855095) * 10 ^ 70 +
        2170219986545314249481517047885244016390827769868226716985454796496766) * 10 ^ 70 +
        6354942455124484178850434919450695620659939413651713365589033535878199) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 100 = 23 +
      77 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (228 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_228 :
    recurrence2Scalar1Main.coeff 228 =
      ((((483 * 10 ^ 70 +
        3031979405898075157791891223244305359721713829583295701001729511972507) * 10 ^ 70 +
        6069865157147855497883956142922486564456574595710961427514826088585612) * 10 ^ 70 +
        4431322656276395300164700127286047799925343811412740543314471595786246) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 101 = 23 +
      78 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (229 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_229 :
    recurrence2Scalar1Main.coeff 229 =
      -((((829 * 10 ^ 70 +
        6595337086387056851058053599683650021749008463732077293475977253171831) * 10 ^ 70 +
        3824600843762811612724134795372940543747942374695603190910607650705493) * 10 ^ 70 +
        6360054794186721308298492990998221031961480836754817904296549170532590) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 102 = 23 +
      79 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (230 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_230 :
    recurrence2Scalar1Main.coeff 230 =
      ((((1282 * 10 ^ 70 +
        4341672815820912171872857424842302578619068161449149253864110385142464) * 10 ^ 70 +
        3736210345187895443234007679822742115134708793769274240756987794429836) * 10 ^ 70 +
        1472863046149323175551681990029578979034871539135913898053036230934065) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 103 = 23 +
      80 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (231 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_231 :
    recurrence2Scalar1Main.coeff 231 =
      -((((1829 * 10 ^ 70 +
        6833086370342075237084479000343920656017088797920936700748844660287278) * 10 ^ 70 +
        6097211672280311118618984177544643173945154364888192031180597966354163) * 10 ^ 70 +
        4752142676953896282593322828581396999916524263861180424734883093696803) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 104 = 23 +
      81 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (232 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_232 :
    recurrence2Scalar1Main.coeff 232 =
      ((((2440 * 10 ^ 70 +
        6404195417811885287523562130965247187153091512682589972111119885448072) * 10 ^ 70 +
        8073436129085885405907242249155482435262034675780470733833106291892331) * 10 ^ 70 +
        9492491205750292644735464852484271343847286386675726818799272311078901) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 105 = 23 +
      82 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (233 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_233 :
    recurrence2Scalar1Main.coeff 233 =
      -((((3065 * 10 ^ 70 +
        8167101879986834998305243149704569943811437122199497521662321553391711) * 10 ^ 70 +
        4374977798092868317984829257224832631530477612874177845959407630023586) * 10 ^ 70 +
        7719157549565329454516225942597257467699803488604657923096787448026777) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 23 +
      83 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Main_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (234 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_234 :
    recurrence2Scalar1Main.coeff 234 =
      ((((3641 * 10 ^ 70 +
        1590124141371229042657258950066280853577840209498475565439355878163277) * 10 ^ 70 +
        4973105433094246749726423011822273529468643290291364906524724688044419) * 10 ^ 70 +
        8640922430853500488385399789856413435714008778745571682418072634818589) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 1 +
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
    rw [show 106 = 22 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
