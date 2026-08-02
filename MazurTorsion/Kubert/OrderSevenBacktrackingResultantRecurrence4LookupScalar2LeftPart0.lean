/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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
  recurrence4LeadingSquare_coeff_0
  recurrence4LeadingSquare_coeff_1
  recurrence4LeadingSquare_coeff_10
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101

attribute [local simp]
  recurrence4LeadingSquare_coeff_102
  recurrence4LeadingSquare_coeff_103
  recurrence4LeadingSquare_coeff_104
  recurrence4LeadingSquare_coeff_105
  recurrence4LeadingSquare_coeff_106
  recurrence4LeadingSquare_coeff_107
  recurrence4LeadingSquare_coeff_108
  recurrence4LeadingSquare_coeff_109
  recurrence4LeadingSquare_coeff_11
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
  recurrence4LeadingSquare_coeff_12
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
  recurrence4LeadingSquare_coeff_13
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
  recurrence4LeadingSquare_coeff_14
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
  recurrence4LeadingSquare_coeff_15
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
  recurrence4LeadingSquare_coeff_16

attribute [local simp]
  recurrence4LeadingSquare_coeff_160
  recurrence4LeadingSquare_coeff_161
  recurrence4LeadingSquare_coeff_162
  recurrence4LeadingSquare_coeff_163
  recurrence4LeadingSquare_coeff_164
  recurrence4LeadingSquare_coeff_165
  recurrence4LeadingSquare_coeff_166
  recurrence4LeadingSquare_coeff_167
  recurrence4LeadingSquare_coeff_168
  recurrence4LeadingSquare_coeff_169
  recurrence4LeadingSquare_coeff_17
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
  recurrence4LeadingSquare_coeff_18
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
  recurrence4LeadingSquare_coeff_19
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
  recurrence4LeadingSquare_coeff_2
  recurrence4LeadingSquare_coeff_20
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
  recurrence4LeadingSquare_coeff_21
  recurrence4LeadingSquare_coeff_210
  recurrence4LeadingSquare_coeff_211
  recurrence4LeadingSquare_coeff_212
  recurrence4LeadingSquare_coeff_213
  recurrence4LeadingSquare_coeff_214
  recurrence4LeadingSquare_coeff_215
  recurrence4LeadingSquare_coeff_216
  recurrence4LeadingSquare_coeff_217

attribute [local simp]
  recurrence4LeadingSquare_coeff_218
  recurrence4LeadingSquare_coeff_219
  recurrence4LeadingSquare_coeff_22
  recurrence4LeadingSquare_coeff_220
  recurrence4LeadingSquare_coeff_221
  recurrence4LeadingSquare_coeff_222
  recurrence4LeadingSquare_coeff_223
  recurrence4LeadingSquare_coeff_23
  recurrence4LeadingSquare_coeff_24
  recurrence4LeadingSquare_coeff_25
  recurrence4LeadingSquare_coeff_26
  recurrence4LeadingSquare_coeff_27
  recurrence4LeadingSquare_coeff_28
  recurrence4LeadingSquare_coeff_29
  recurrence4LeadingSquare_coeff_3
  recurrence4LeadingSquare_coeff_30
  recurrence4LeadingSquare_coeff_31
  recurrence4LeadingSquare_coeff_32
  recurrence4LeadingSquare_coeff_33
  recurrence4LeadingSquare_coeff_34
  recurrence4LeadingSquare_coeff_35
  recurrence4LeadingSquare_coeff_36
  recurrence4LeadingSquare_coeff_37
  recurrence4LeadingSquare_coeff_38
  recurrence4LeadingSquare_coeff_39
  recurrence4LeadingSquare_coeff_4
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
  recurrence4LeadingSquare_coeff_5
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
  recurrence4LeadingSquare_coeff_6
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
  recurrence4LeadingSquare_coeff_7
  recurrence4LeadingSquare_coeff_70
  recurrence4LeadingSquare_coeff_71
  recurrence4LeadingSquare_coeff_72
  recurrence4LeadingSquare_coeff_73
  recurrence4LeadingSquare_coeff_74

attribute [local simp]
  recurrence4LeadingSquare_coeff_75
  recurrence4LeadingSquare_coeff_76
  recurrence4LeadingSquare_coeff_77
  recurrence4LeadingSquare_coeff_78
  recurrence4LeadingSquare_coeff_79
  recurrence4LeadingSquare_coeff_8
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
  recurrence4LeadingSquare_coeff_9
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

theorem recurrence4Scalar2Left_coeff_0 :
    recurrence4Scalar2Left.coeff 0 =
      (-127471115825187632452307041285142471049216 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_1 :
    recurrence4Scalar2Left.coeff 1 =
      (-4011287777375747889525563116007642725524910080 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_2 :
    recurrence4Scalar2Left.coeff 2 =
      (28334011706938345927449892455348506877518871478272 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_3 :
    recurrence4Scalar2Left.coeff 3 =
      (-75630802208780268109721094093080497550916989135089920 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_4 :
    recurrence4Scalar2Left.coeff 4 =
      (94787890866504242515279295282874591979474130167469907456 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_5 :
    recurrence4Scalar2Left.coeff 5 =
      (-31051920582379933833806066663955829847410340960780278197360 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_6 :
    recurrence4Scalar2Left.coeff 6 =
      (-67776221530991344021875761982119277564688026621567849821913720 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_7 :
    recurrence4Scalar2Left.coeff 7 =
      (102304347298346249538311221130900816986823440125823092518720718960 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_8 :
    recurrence4Scalar2Left.coeff 8 =
      (-67194063918792685662737783584772845681391094933258357189361624294636 : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_9 :
    recurrence4Scalar2Left.coeff 9 =
      ((2 * 10 ^ 70 +
        9648442864474559438266783872790027333546290228212153356813488638542756) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_10 :
    recurrence4Scalar2Left.coeff 10 =
      -((1423 * 10 ^ 70 +
        9259984208895214042128940295111627849375819377242617750960343399814024) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_11 :
    recurrence4Scalar2Left.coeff 11 =
      ((674031 * 10 ^ 70 +
        0581304485347317387099952708724950069768683086450319455437158094490376) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_12 :
    recurrence4Scalar2Left.coeff 12 =
      -((161559662 * 10 ^ 70 +
        9552042877844065750738872019814393188081950396019973333460338309552400) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_13 :
    recurrence4Scalar2Left.coeff 13 =
      -((39672410627 * 10 ^ 70 +
        7615599190959447665933412673514209220750138246818455562178426581911596) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_14 :
    recurrence4Scalar2Left.coeff 14 =
      ((51257845862576 * 10 ^ 70 +
        8377826215875843487505891526062998373564581956171102260020946054354768) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_15 :
    recurrence4Scalar2Left.coeff 15 =
      -((26099663116032402 * 10 ^ 70 +
        1502858717619982664727236924939331117025947661556589279414922984906568) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_16 :
    recurrence4Scalar2Left.coeff 16 =
      ((11144958915896891718 * 10 ^ 70 +
        0958892645422579138077265920450098006637737797702115676667477813492994) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_17 :
    recurrence4Scalar2Left.coeff 17 =
      -((4370890525831241268216 * 10 ^ 70 +
        8222065355369929179157830621831687092046099195241918405650086623733620) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_18 :
    recurrence4Scalar2Left.coeff 18 =
      ((1241820230962625091076560 * 10 ^ 70 +
        8141638997689085444700369815948083168709228901164633106774764427573349) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_19 :
    recurrence4Scalar2Left.coeff 19 =
      -((91034008276239700626494960 * 10 ^ 70 +
        0049974723408091175836496735671338190589591911745122474233313778291775) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_20 :
    recurrence4Scalar2Left.coeff 20 =
      -((124340426828166323942689980865 * 10 ^ 70 +
        4977243212922904439553506822894768734325076540465260952328134300693406) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_21 :
    recurrence4Scalar2Left.coeff 21 =
      ((79898907445031000840642898095322 * 10 ^ 70 +
        1701685893348849204529165255009325486372851914109468510908519936690984) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_22 :
    recurrence4Scalar2Left.coeff 22 =
      -((28905252793433204471271967560440964 * 10 ^ 70 +
        1969238175942713719178633339829572539489101630060927636548779318932529) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_23 :
    recurrence4Scalar2Left.coeff 23 =
      ((7356234922660298507199385596096397593 * 10 ^ 70 +
        2382081344417936805732602865410025352014499941247677958618175532085121) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_24 :
    recurrence4Scalar2Left.coeff 24 =
      -((1303886409209882505005350278249406552131 * 10 ^ 70 +
        4396326234895596387652222309791593204445535661041643748408895731571250) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_25 :
    recurrence4Scalar2Left.coeff 25 =
      ((97071983233125920632982164985796267326739 * 10 ^ 70 +
        3931092016764537652425191725234001892976603629700565221935287878678269) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_26 :
    recurrence4Scalar2Left.coeff 26 =
      ((41148810992278701370684014544631831108704160 * 10 ^ 70 +
        6727363433926234196944374078754695935815019806461452765617011812704319) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_27 :
    recurrence4Scalar2Left.coeff 27 =
      -((25262272205198095247897385149651140959765386565 * 10 ^ 70 +
        3040349337406841674299671366905712662060971010413602828573850626151161) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_28 :
    recurrence4Scalar2Left.coeff 28 =
      ((9005914526816815783203355969342176787092637587205 * 10 ^ 70 +
        9075572529378644068291023612136747416891177748792989766631791132248909) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_29 :
    recurrence4Scalar2Left.coeff 29 =
      -((2537308641182017784744572152799995047421667433251387 * 10 ^ 70 +
        8981028089486620733481792562235888671944786167383351748226016105398300) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_30 :
    recurrence4Scalar2Left.coeff 30 =
      ((603562515222327963840277594685169553407484217143274353 * 10 ^ 70 +
        7736353045568933365599083257702169207185186308769847467521851093303069) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_31 :
    recurrence4Scalar2Left.coeff 31 =
      -((123817419619583759609597519860585689415472868050874138606 * 10 ^ 70 +
        4878562555992567337773135403079899355176133191515881459324631971581189) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_32 :
    recurrence4Scalar2Left.coeff 32 =
      ((22050147475317731493710158495786860716375682820519883343657 * 10 ^ 70 +
        8272970705158648691700191850024098513252843324545852039603118213345837) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (32 - x)) = _
  rw [show 33 = 0 +
    33 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_33 :
    recurrence4Scalar2Left.coeff 33 =
      -((3402923859643917907377609157491216900417538774268581957380433 * 10 ^ 70 +
        9280404131233200834147716758172786443141460104045318410738274072035894) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (33 - x)) = _
  rw [show 34 = 0 +
    34 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_34 :
    recurrence4Scalar2Left.coeff 34 =
      ((449857433875838971282778545928556834828882574625793021222686838 * 10 ^ 70 +
        6950485049242012330813459377191232934596763922716635044926132418011021) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (34 - x)) = _
  rw [show 35 = 0 +
    35 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_35 :
    recurrence4Scalar2Left.coeff 35 =
      -((49374253151591346324996879222659457903257972638594217297174798995 * 10 ^ 70 +
        0125834641441611741431819576349236622171764337116875667268733997623437) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (35 - x)) = _
  rw [show 36 = 0 +
    36 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_36 :
    recurrence4Scalar2Left.coeff 36 =
      ((4110727399433705882439304943428494017931531629871866626751170574691 * 10 ^ 70 +
        8282262828515247883526078143513606672801538767530069637115475029193073) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (36 - x)) = _
  rw [show 37 = 0 +
    37 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_37 :
    recurrence4Scalar2Left.coeff 37 =
      -((165428576986449962901700039759957175231443500402056219960219344454540 * 10 ^ 70 +
        9136788235846231138574117833270052417911603811458340482431771720149016) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (37 - x)) = _
  rw [show 38 = 0 +
    38 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_38 :
    recurrence4Scalar2Left.coeff 38 =
      -(((2 * 10 ^ 70 +
        2568663113482297816379502696960321307664238215183382941320853347331683) * 10 ^ 70 +
        3019566076465230093843961798658260267666735421018529328210975716048015) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (38 - x)) = _
  rw [show 39 = 0 +
    39 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_39 :
    recurrence4Scalar2Left.coeff 39 =
      (((680 * 10 ^ 70 +
        6193779925468254385975643507355514142911410888908966841534634175254992) * 10 ^ 70 +
        1504172669142818949865774577003173864674739960183319156818708869511341) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (39 - x)) = _
  rw [show 40 = 0 +
    40 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_40 :
    recurrence4Scalar2Left.coeff 40 =
      -(((107432 * 10 ^ 70 +
        0466239045769447370109150022759829160612490970353627659620895411805476) * 10 ^ 70 +
        6519989954596023800713929641002258585052260867552248810262428892157760) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (40 - x)) = _
  rw [show 41 = 0 +
    41 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_41 :
    recurrence4Scalar2Left.coeff 41 =
      (((12846234 * 10 ^ 70 +
        4482036918481258330046683458690828538955404101840821667204279459640206) * 10 ^ 70 +
        8369842088445867914860291516694133960566685079157512516080000763205990) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (41 - x)) = _
  rw [show 42 = 0 +
    42 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_42 :
    recurrence4Scalar2Left.coeff 42 =
      -(((1242214030 * 10 ^ 70 +
        0268734753471160810256266080156464116494797311231177080886840639570292) * 10 ^ 70 +
        5724976758756262845956359597776552586612381855506065092381207374176838) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (42 - x)) = _
  rw [show 43 = 0 +
    43 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_43 :
    recurrence4Scalar2Left.coeff 43 =
      (((95867665703 * 10 ^ 70 +
        8678962945931966795884869424738275190184678028441937734723175044607403) * 10 ^ 70 +
        2152992922448835879162220044518542354700146146109112107960064712321781) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (43 - x)) = _
  rw [show 44 = 0 +
    44 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_44 :
    recurrence4Scalar2Left.coeff 44 =
      -(((5189693910657 * 10 ^ 70 +
        8289050677532400687440077088356197161286623312899687482396375606508674) * 10 ^ 70 +
        2535425849821785766638908889616178617177808655932111151008360493752159) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (44 - x)) = _
  rw [show 45 = 0 +
    45 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_45 :
    recurrence4Scalar2Left.coeff 45 =
      (((44306103007312 * 10 ^ 70 +
        7799290459414930800808397495492325616454354876723067430863921283228034) * 10 ^ 70 +
        3234515502168156450022576804499774146317806620269744960720391034096430) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (45 - x)) = _
  rw [show 46 = 0 +
    46 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_46 :
    recurrence4Scalar2Left.coeff 46 =
      (((35414304331445591 * 10 ^ 70 +
        5476640261766934731214690428068334792787361208834201900031988698665214) * 10 ^ 70 +
        2982924034170457717428205077203906731252271562471453325262498076084475) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (46 - x)) = _
  rw [show 47 = 0 +
    47 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_47 :
    recurrence4Scalar2Left.coeff 47 =
      -(((6090839925826557741 * 10 ^ 70 +
        8030499160827078895069086707383779706105803398501352825242552619336862) * 10 ^ 70 +
        7082438326572370476184371775004511678065194858470853561842220926379666) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (47 - x)) = _
  rw [show 48 = 0 +
    48 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_48 :
    recurrence4Scalar2Left.coeff 48 =
      (((707139799729792401072 * 10 ^ 70 +
        9116225173921139373704013551871319032429290513495751669761522689966302) * 10 ^ 70 +
        6200124127099086387799558698639840346940445810405910654771949285186562) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (48 - x)) = _
  rw [show 49 = 0 +
    49 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_49 :
    recurrence4Scalar2Left.coeff 49 =
      -(((67734958252993813527985 * 10 ^ 70 +
        5348991229673209059267024411338398170436896031904421932800420552464270) * 10 ^ 70 +
        9508809034752443628377368128431862907635108127603290839483944816815843) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (49 - x)) = _
  rw [show 50 = 0 +
    50 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_50 :
    recurrence4Scalar2Left.coeff 50 =
      (((5690793434313301367598691 * 10 ^ 70 +
        4504136778965477628939469857491586948465704664877103225965239860723750) * 10 ^ 70 +
        5184241133307778396751715489844800700486030005527786623108474826964860) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (50 - x)) = _
  rw [show 51 = 0 +
    51 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_51 :
    recurrence4Scalar2Left.coeff 51 =
      -(((431131362854304677208996370 * 10 ^ 70 +
        0519775262790521175143689145941487064654378131619521493856705277736779) * 10 ^ 70 +
        6854133854484070932650582082673608725409583304980029468588439708675653) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (51 - x)) = _
  rw [show 52 = 0 +
    52 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_52 :
    recurrence4Scalar2Left.coeff 52 =
      (((29906863867243839986240757446 * 10 ^ 70 +
        5347254779043115475551000547968233107448105797697320032322569017350082) * 10 ^ 70 +
        2462591106904302510644765899333190987907919584849910971347998577210219) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (52 - x)) = _
  rw [show 53 = 0 +
    53 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_53 :
    recurrence4Scalar2Left.coeff 53 =
      -(((1917874575742775415377581014009 * 10 ^ 70 +
        3147835025495337820209236597380085603101034649496080039489596327194578) * 10 ^ 70 +
        2056169059121160957699180799765501609885385758916253207935900201803179) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (53 - x)) = _
  rw [show 54 = 0 +
    54 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_54 :
    recurrence4Scalar2Left.coeff 54 =
      (((114445292974590483979316725546876 * 10 ^ 70 +
        1920502175581175794903574946557529319559277570361889020936523145696183) * 10 ^ 70 +
        2893301687822865618065323907467731544478299558287524302293986701352351) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (54 - x)) = _
  rw [show 55 = 0 +
    55 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_55 :
    recurrence4Scalar2Left.coeff 55 =
      -(((6385049195718394969251400924123849 * 10 ^ 70 +
        0887184471287043240652038567485331015832875026504144830645043483441488) * 10 ^ 70 +
        2879701227710833525572363557882031166110014808322665759037665037021512) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (55 - x)) = _
  rw [show 56 = 0 +
    56 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_56 :
    recurrence4Scalar2Left.coeff 56 =
      (((334258236692572019299040636650497249 * 10 ^ 70 +
        6591005703888871253125567186026518718353913947129066110678163665849995) * 10 ^ 70 +
        8438059673289864499114574445532857732673998083209178551739430020734484) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (56 - x)) = _
  rw [show 57 = 0 +
    57 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_57 :
    recurrence4Scalar2Left.coeff 57 =
      -(((16465571304902050102914474915265233708 * 10 ^ 70 +
        8715155192118156909020618867876478745499772853315928958977583981621494) * 10 ^ 70 +
        9553661822818319552586531367611674217648012036481831841639392685007732) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (57 - x)) = _
  rw [show 58 = 0 +
    58 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_58 :
    recurrence4Scalar2Left.coeff 58 =
      (((764946505421988680742659982152060323838 * 10 ^ 70 +
        5503345732903235283738839057419394305267461655198382240297096783860779) * 10 ^ 70 +
        5606815596821921777815637880952246744449220872084342602895199570120632) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (58 - x)) = _
  rw [show 59 = 0 +
    59 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_59 :
    recurrence4Scalar2Left.coeff 59 =
      -(((33577187869343965821485586534901868961735 * 10 ^ 70 +
        4811775196380337137070087587382409662942903573452791875612486710791222) * 10 ^ 70 +
        1450084233020131282875120408550446065458232732766618142578619681300222) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (59 - x)) = _
  rw [show 60 = 0 +
    60 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_60 :
    recurrence4Scalar2Left.coeff 60 =
      (((1394665828269289379653343442954617471117548 * 10 ^ 70 +
        6357290465927037595448799696075617733263273168394890487755913377926213) * 10 ^ 70 +
        3297585293568725233607171068084307698963877089141482261483949451081743) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (60 - x)) = _
  rw [show 61 = 0 +
    61 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_61 :
    recurrence4Scalar2Left.coeff 61 =
      -(((54883262492731551313231587249795758899531623 * 10 ^ 70 +
        8738968331213913567889342434104914254888435224871186907475164594276409) * 10 ^ 70 +
        1698300947234122298513148615638549613214303870743130201719457971634924) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (61 - x)) = _
  rw [show 62 = 0 +
    62 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_62 :
    recurrence4Scalar2Left.coeff 62 =
      (((2048219759157736260968817657524298266772227188 * 10 ^ 70 +
        3130244685353673970701173925200568709270130680561701121946633507969617) * 10 ^ 70 +
        5038847016014846447573300795814684623519153165125058501203906497916672) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (62 - x)) = _
  rw [show 63 = 0 +
    63 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_63 :
    recurrence4Scalar2Left.coeff 63 =
      -(((72543913268071684758729822390641690936796417765 * 10 ^ 70 +
        3817380150287380288293052056233596166024137756883965915157284446975953) * 10 ^ 70 +
        9941870353879462865932551357810498397940415636903141046446921655004739) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (63 - x)) = _
  rw [show 64 = 0 +
    64 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_64 :
    recurrence4Scalar2Left.coeff 64 =
      (((2439674106525211978404246556138789866204571347436 * 10 ^ 70 +
        6529285846236082228315879099973159117426110506963554041306337521704740) * 10 ^ 70 +
        8054290211381522917257675841123206986184149341073848983407940503465845) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (64 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_65 :
    recurrence4Scalar2Left.coeff 65 =
      -(((77925255789443283630190610766607318964643835628712 * 10 ^ 70 +
        8017574595094827210448899175666015152907363413837734405931399882396974) * 10 ^ 70 +
        2339168830384730399517785503793968898143950830083801551712810552396953) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (65 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_66 :
    recurrence4Scalar2Left.coeff 66 =
      (((2363875652642438828236493330131617938399401334486753 * 10 ^ 70 +
        6717644172291494074204428062063061631308189051793727356571366520396951) * 10 ^ 70 +
        6605166924180720437726156568804638020824133173076223177579737152110085) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (66 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_67 :
    recurrence4Scalar2Left.coeff 67 =
      -(((68077578926451852760230597081651782261058397321461201 * 10 ^ 70 +
        3528502590949197925317991953331209759327028419129171603146176437088882) * 10 ^ 70 +
        3654101433908978323414897869041783622180447540208984417736013950778009) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (67 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_68 :
    recurrence4Scalar2Left.coeff 68 =
      (((1859753236136341168239241662733337620591809470868899388 * 10 ^ 70 +
        5080990556356758508720971100386909231771953018343480254539463689907461) * 10 ^ 70 +
        0745976115638343300801939024196589641785345922789809688117903238374770) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (68 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_69 :
    recurrence4Scalar2Left.coeff 69 =
      -(((48122967288780351018591605936409355067228508603791961356 * 10 ^ 70 +
        9663832344992795995115301324208693680949007011280331815526669562254026) * 10 ^ 70 +
        8117878236438904573623140687289713987433074183797212440430635167328202) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (69 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_70 :
    recurrence4Scalar2Left.coeff 70 =
      (((1176760832654252751429112440522423692273319961021642456946 * 10 ^ 70 +
        4049356999854139738170761974702821135521708564145554451960423894577545) * 10 ^ 70 +
        8551977030533907889577592019029220416699458686973953859683889307865831) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (70 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_71 :
    recurrence4Scalar2Left.coeff 71 =
      -(((27093880938772842999690187264454422505581893482066607426731 * 10 ^ 70 +
        5749109950408137145751503169245769078842286713700017956765534327429086) * 10 ^ 70 +
        5049586396947596124436256629883670927683474055622766605711572300864655) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (71 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_72 :
    recurrence4Scalar2Left.coeff 72 =
      (((583912703234880650129817977389271424257154968675827124101602 * 10 ^ 70 +
        5992038664233884936577758891254238549354428456041201014990563264039934) * 10 ^ 70 +
        6084242172207584821930506290281309043971319551514795227554756351000791) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (72 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_73 :
    recurrence4Scalar2Left.coeff 73 =
      -(((11663669012556926490558972641431888626830924888190478239550702 * 10 ^ 70 +
        3978096754570327447100802148309083550364108230694908105473320985521965) * 10 ^ 70 +
        0916199520873351679484520151088160383991289559980962650994978677293499) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (73 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_74 :
    recurrence4Scalar2Left.coeff 74 =
      (((212104744881792411220465544131276527396018065357277540164813882 * 10 ^ 70 +
        5848670294775171951562086658960612877563832915105896213900731632437807) * 10 ^ 70 +
        3310011613753924417510050740845873585424917280298531869648822102966961) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (74 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_75 :
    recurrence4Scalar2Left.coeff 75 =
      -(((3382892094323677077498499411785068752154486617769603620291605434 * 10 ^ 70 +
        6696277095643278209109210399389618097174997600512791580136313027721715) * 10 ^ 70 +
        7441543812853155115450465439030173411498465394253189289465179572657005) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (75 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_76 :
    recurrence4Scalar2Left.coeff 76 =
      (((42814478698060027065747631158242169114623904494698146806612926290 * 10 ^ 70 +
        0788175736437358971546292710965479483477822586723264160261857938450554) * 10 ^ 70 +
        1279879338088271584499618006626346185193031753846709554712145291008601) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (76 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_77 :
    recurrence4Scalar2Left.coeff 77 =
      -(((255442761470350619540808635529578711308205721032497045174876495081 * 10 ^ 70 +
        4915202452369735773465093085036563756143020417564164958952642089255916) * 10 ^ 70 +
        7499499108634377670252911186308059144087134982617307508142221079904871) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (77 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_78 :
    recurrence4Scalar2Left.coeff 78 =
      -(((7583752459860640955375517413014849740261326852965864607448932302621 * 10 ^ 70 +
        6198620499779736993828395628754457184429228710220613120938305974203310) * 10 ^ 70 +
        8423501930652544663017135881197818317591031332597768503808467801452199) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (78 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_79 :
    recurrence4Scalar2Left.coeff 79 =
      (((387549441607095765138658146740426156995284197304701821723396643060476 * 10 ^ 70 +
        6954652661835709693432650222400180950789019823811715303779840730422786) * 10 ^ 70 +
        6630923950145413181409435331426429131976893922016463509700158429949709) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (79 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_80 :
    recurrence4Scalar2Left.coeff 80 =
      -((((1 * 10 ^ 70 +
        1529957164402304205476867275009964844532412576155459414446668688971811) * 10 ^ 70 +
        9514058121083055744183448808977741920328488352222130853515944773793215) * 10 ^ 70 +
        1999791670234815784601142215342217177880617848556144105987937590319101) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (80 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_81 :
    recurrence4Scalar2Left.coeff 81 =
      ((((27 * 10 ^ 70 +
        9018166757525326534972285482788686368387291333837184718709445412447229) * 10 ^ 70 +
        7864021229789842214557010017624495665698549481076647150981945574276570) * 10 ^ 70 +
        6614876327308606545928411684197667156474957994614605377953443957556027) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (81 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_82 :
    recurrence4Scalar2Left.coeff 82 =
      -((((592 * 10 ^ 70 +
        9991667555225273601284501840873032475776200051395928486295672447672013) * 10 ^ 70 +
        2293087462494261779667618282971184970869841332807249305564485120441407) * 10 ^ 70 +
        2788634067564352988353109471057617674305443620993795914876806663791230) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (82 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_83 :
    recurrence4Scalar2Left.coeff 83 =
      ((((11369 * 10 ^ 70 +
        5889830164466699110755230950301656463504953978481814944253497441512260) * 10 ^ 70 +
        1037039148716869989134798772909712853144816257522399971596439102740026) * 10 ^ 70 +
        2750335024299635197242011532307237066647764523200311878247399043878379) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (83 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_84 :
    recurrence4Scalar2Left.coeff 84 =
      -((((198160 * 10 ^ 70 +
        4361756940869960725560846584268464043895403150609125850386493540237857) * 10 ^ 70 +
        1273659763537023891160878258563037311103929069393554180550112831899156) * 10 ^ 70 +
        9725848513653151110892813254640585411116371524133023929850404858213554) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (84 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_85 :
    recurrence4Scalar2Left.coeff 85 =
      ((((3121757 * 10 ^ 70 +
        5909194463301779175031588718690470669741501223496681797763112503288628) * 10 ^ 70 +
        2998265306905054083388109160888044644753277625697084052549738256151018) * 10 ^ 70 +
        1922406731752678501739024004740298853210442219625904291574872173913274) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (85 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_86 :
    recurrence4Scalar2Left.coeff 86 =
      -((((43397967 * 10 ^ 70 +
        8043727019572764101667379154208565666656396798455679072272871424188162) * 10 ^ 70 +
        0978063413567645845877071904760900598987584956738985461477507792342220) * 10 ^ 70 +
        2077545195662967820474357726806289631359383999867299158493576358047516) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (86 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_87 :
    recurrence4Scalar2Left.coeff 87 =
      ((((496547679 * 10 ^ 70 +
        1657364079073749079124063763401016347090660315675612051108029495234412) * 10 ^ 70 +
        9076456198837480893590836005847399168972344197152068810689122542543917) * 10 ^ 70 +
        4296915522350915638210869732983671621825165650686891677546459422125324) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (87 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_88 :
    recurrence4Scalar2Left.coeff 88 =
      -((((3500201449 * 10 ^ 70 +
        7248935750867558863732933238474798678978924207270817458349419901861067) * 10 ^ 70 +
        0662132829053428506148363419120894540025757363521291624833203720091555) * 10 ^ 70 +
        5996232916867769283989317149287154936313250882961620287848782097604098) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (88 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_89 :
    recurrence4Scalar2Left.coeff 89 =
      -((((29109080336 * 10 ^ 70 +
        5735189335020930586722668004529013231067989369296545827154000052473619) * 10 ^ 70 +
        2974251041173561869853964652004759379256987684718290979566164334361339) * 10 ^ 70 +
        0871517434000593034001858412142491987218564642486023736825223868047727) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (89 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_90 :
    recurrence4Scalar2Left.coeff 90 =
      ((((1914239047201 * 10 ^ 70 +
        3509784626628093838258321417281626450626749703645123520725702237978583) * 10 ^ 70 +
        5487274495340388879038813086781175328157468437449807205265412598790280) * 10 ^ 70 +
        7846307956945712319713399962629000170569784810629440988970365845671052) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (90 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_91 :
    recurrence4Scalar2Left.coeff 91 =
      -((((52817727027441 * 10 ^ 70 +
        4605799381953573638234283028295600660897694895327216393592810767518739) * 10 ^ 70 +
        4400743348128293868445478906789933941150271688381113736324739570350779) * 10 ^ 70 +
        4049935643736063661958957348381081044884597585264398424286122466584852) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (91 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_92 :
    recurrence4Scalar2Left.coeff 92 =
      ((((1149682724177960 * 10 ^ 70 +
        5659096882805570673221802295844566885505607509480154753514730141032713) * 10 ^ 70 +
        1348511230772411045625515908037142076152154566269003797693923581768780) * 10 ^ 70 +
        4681812967809014728618973214585600159324348313157615088818926328376043) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (92 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_93 :
    recurrence4Scalar2Left.coeff 93 =
      -((((22041900693560654 * 10 ^ 70 +
        2378434788930000712635731292207637338394897214650283209451902079757818) * 10 ^ 70 +
        5540401433727233946777641462072157542646289552787094883914867050793134) * 10 ^ 70 +
        0177737043277161131653274832287492029494107639083297504771396073013168) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (93 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_94 :
    recurrence4Scalar2Left.coeff 94 =
      ((((387653979741816224 * 10 ^ 70 +
        5545408910267653254250638898843944555017842048891100356899284936253107) * 10 ^ 70 +
        2223971395417668279736275882222772104111965838717892363040928609092647) * 10 ^ 70 +
        1210635134568182777901123708304876520575553832735179389311409866565231) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (94 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_95 :
    recurrence4Scalar2Left.coeff 95 =
      -((((6379181982276583391 * 10 ^ 70 +
        5269467068850173494072608351433782828794327415179843294838968004203748) * 10 ^ 70 +
        0483378502368287752244722700813265589918210459264396140547656757076890) * 10 ^ 70 +
        4759916550299759122148140737405646644185694299682054835433868022343845) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (95 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_96 :
    recurrence4Scalar2Left.coeff 96 =
      ((((99338659834711965708 * 10 ^ 70 +
        6052161996615703403747106469232611655707313518576138664489593060633784) * 10 ^ 70 +
        7784075089285491629400150473444697287991249581075658629358108307271445) * 10 ^ 70 +
        4313553709748737257830235147312137177730103342332253013992685532650451) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (96 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_97 :
    recurrence4Scalar2Left.coeff 97 =
      -((((1474382525708973097700 * 10 ^ 70 +
        8842472327012363962417812319270745390837281312792359285465393296675497) * 10 ^ 70 +
        2954459974470880995239056093505342788536069808103497977465353123182321) * 10 ^ 70 +
        1083479434957655210155996815805865027058839544555288878793873083247950) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (97 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_98 :
    recurrence4Scalar2Left.coeff 98 =
      ((((20958435204762057318184 * 10 ^ 70 +
        1967816354337455328286707018634093516911467794331894838187718349831530) * 10 ^ 70 +
        2285312595206862205485355781731539974868578038846324736284223762800527) * 10 ^ 70 +
        2384165692697320606768118540201140848694732440911782613973178974598969) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (98 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_99 :
    recurrence4Scalar2Left.coeff 99 =
      -((((286347148810756852664112 * 10 ^ 70 +
        4510496609172852892537043220161458355233618972754072231936801443321333) * 10 ^ 70 +
        7010148425681177952818197894517857983150675064691690776799263898907109) * 10 ^ 70 +
        8520352098203129787804916933501169217978010806617948127050542171890290) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (99 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_100 :
    recurrence4Scalar2Left.coeff 100 =
      ((((3770207911156485421144898 * 10 ^ 70 +
        4690410561961825755883039018998963244100377180041597361274869376076675) * 10 ^ 70 +
        1967422677837153239890907988077176260266870520594953531505654111980954) * 10 ^ 70 +
        4673205125660095807059964585640954600254454053372252488285566405859038) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (100 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_101 :
    recurrence4Scalar2Left.coeff 101 =
      -((((47937770137442780277175862 * 10 ^ 70 +
        1737641831371867317782156473768424897774810484765954077820406186645372) * 10 ^ 70 +
        2589348483028854154545976985209069261005203280264694456579565753742435) * 10 ^ 70 +
        0352039366250712120519717266465012985175451178716009949310822700847793) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (101 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_102 :
    recurrence4Scalar2Left.coeff 102 =
      ((((589598890912392706798005466 * 10 ^ 70 +
        8860509017990760913242521251553418536820658573121593924937990371727080) * 10 ^ 70 +
        2254834456357352245910102569552896358792063381086627591673044336371630) * 10 ^ 70 +
        9875874099605724636446937978593784062770101933998627841562081575790047) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (102 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_103 :
    recurrence4Scalar2Left.coeff 103 =
      -((((7024272109206125598638453530 * 10 ^ 70 +
        3792694368561464141607692611992781387417559062997830615487594452749753) * 10 ^ 70 +
        9342576904833041479634443344818419040590767326493051067452269673953116) * 10 ^ 70 +
        6873604473566959404676776740378941468216932347682998795714777550692253) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (103 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_104 :
    recurrence4Scalar2Left.coeff 104 =
      ((((81155368592524536124881623548 * 10 ^ 70 +
        5007425627440295575257638116711466922885080497852305402044351808850347) * 10 ^ 70 +
        0209765048227432299310730987645771470468810379341554156479599262441257) * 10 ^ 70 +
        6590142234556365515936208516244201883030141920300996005559663447493014) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (104 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_105 :
    recurrence4Scalar2Left.coeff 105 =
      -((((910202822267715639251268723229 * 10 ^ 70 +
        0402630073830481259461928752488306789859244002011609389629137421229874) * 10 ^ 70 +
        0926653314006559858392968614007745198040749149976196123052614686075502) * 10 ^ 70 +
        2476415402507247407944100572514327645301395119625597239260983512797909) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (105 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_106 :
    recurrence4Scalar2Left.coeff 106 =
      ((((9918410074981400759835184095792 * 10 ^ 70 +
        5405192062208812983674230881644822968835283761824897749743455462992842) * 10 ^ 70 +
        2223569042518592988333509923288614159461124286185433437764239110516165) * 10 ^ 70 +
        7942931290933180695819372933621316901158067745286170089290314477365236) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (106 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_107 :
    recurrence4Scalar2Left.coeff 107 =
      -((((105090302579582142440557553753078 * 10 ^ 70 +
        5691640444674493025683508030517650202054300763076967479172078409759193) * 10 ^ 70 +
        3051063201064484728597246775366379899316340006541653735197075246021093) * 10 ^ 70 +
        3351241813082027779646392383162110918493368282161250728370732584217125) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (107 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_108 :
    recurrence4Scalar2Left.coeff 108 =
      ((((1083422899436314100545974522098769 * 10 ^ 70 +
        0291333228160355765734556542954159460641612764163488639124894933701593) * 10 ^ 70 +
        5867988436038781420578069649163022187345973927813986186161991804214621) * 10 ^ 70 +
        9219595239350572037894084693997052690481296167097095325662468073204236) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (108 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_109 :
    recurrence4Scalar2Left.coeff 109 =
      -((((10874694623910869343601605914588145 * 10 ^ 70 +
        9523416501956151038999178931548865638333993783934634555493853695731337) * 10 ^ 70 +
        2445628917826548609319176605088563205783504899725798482008864135083320) * 10 ^ 70 +
        2238970674516698656397855222139140158726092705178496623970709010993818) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (109 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_110 :
    recurrence4Scalar2Left.coeff 110 =
      ((((106332131670846443830527708142755452 * 10 ^ 70 +
        6339723792891791657440256439563464097317313794921113588874183347936214) * 10 ^ 70 +
        0734092087703807701468644802427446064339369084196566317877372219713950) * 10 ^ 70 +
        6417600124216962431943119594015570552696146614195997864260936432243471) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (110 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_111 :
    recurrence4Scalar2Left.coeff 111 =
      -((((1013362277056368479944492445300338101 * 10 ^ 70 +
        8368090886737583846720872027110477897325165210204196696519530616195957) * 10 ^ 70 +
        8281667829796500480381780534016070516451977061216303598159665882142104) * 10 ^ 70 +
        5188214541088906840613220788165932852049212113582153313688717260623153) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (111 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_112 :
    recurrence4Scalar2Left.coeff 112 =
      ((((9417265624077509129001546027092568334 * 10 ^ 70 +
        3188161013854284672226288254457402690342339093463077854971635483233538) * 10 ^ 70 +
        3268073616529560908731698696466064692155908744719100966099773020853676) * 10 ^ 70 +
        4153179855216000832314674102535594526444867755840888154731330857433427) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (112 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_113 :
    recurrence4Scalar2Left.coeff 113 =
      -((((85376251669017799691458054620771712969 * 10 ^ 70 +
        0039573481339230011173865826182499175223664979104047591717195555172156) * 10 ^ 70 +
        9707468886149189871009934004784030503307336387564145653745662784942475) * 10 ^ 70 +
        3828570522969225263643523753969757089390918927908095006560845125754200) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (113 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_114 :
    recurrence4Scalar2Left.coeff 114 =
      ((((755406995055259544552903021848222920107 * 10 ^ 70 +
        0986022747777160621243712820358489566006061297347881410352522495600377) * 10 ^ 70 +
        3729373355874615482109410512604035253580126712060715050250931326406079) * 10 ^ 70 +
        3980060877211195452361267171314617909830193501003280471520606988520388) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (114 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_115 :
    recurrence4Scalar2Left.coeff 115 =
      -((((6525666137052408126127308018995720884906 * 10 ^ 70 +
        6187024663540072376156372598443618760723723822888130972768169983346784) * 10 ^ 70 +
        7409048821422252964963290724671562459317485230470899389334791440098584) * 10 ^ 70 +
        8618954322899926220423875957336662889349433350054950431932294784458014) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (115 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_116 :
    recurrence4Scalar2Left.coeff 116 =
      ((((55058837878026253142260661871692314719148 * 10 ^ 70 +
        8334847107744163188401381812042036088238628586977692924063703186374428) * 10 ^ 70 +
        2938249130228115408617989287565799529575131818870401994822777911524911) * 10 ^ 70 +
        7150417450921501324100441673409235411602363805627349520596579524138149) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (116 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_117 :
    recurrence4Scalar2Left.coeff 117 =
      -((((453876010942975563580873097492948469918266 * 10 ^ 70 +
        4701372184796775606869179676183653843387234091938218333551410076617545) * 10 ^ 70 +
        2819158424291402325262104181512318021629961184844004396123863380974838) * 10 ^ 70 +
        4201261817746502517794795954732953337918856247839805389154271811321154) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (117 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_118 :
    recurrence4Scalar2Left.coeff 118 =
      ((((3656766724298442209581969079366870000016496 * 10 ^ 70 +
        4397807905690812443647720860218302497104749875307707121745280726133138) * 10 ^ 70 +
        0158137516888351920882188895453548029878812756993663962191484146059971) * 10 ^ 70 +
        5518764690709890373644844804581374857326472182091072017948320997944129) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (118 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_119 :
    recurrence4Scalar2Left.coeff 119 =
      -((((28803278995240404602910037055054632854525975 * 10 ^ 70 +
        4545945021492460912324903249320445456549366382036340228892645311476098) * 10 ^ 70 +
        7782547248174279029635453740047758231502967689735304401513166349925037) * 10 ^ 70 +
        8661085773661663975271318505020375414526040201507779935111226171876948) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (119 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_120 :
    recurrence4Scalar2Left.coeff 120 =
      ((((221870572614778586513638539338155278848153790 * 10 ^ 70 +
        8424457860553692145420631451049551283767127662786788229207644084413851) * 10 ^ 70 +
        5942584233890615918625634313890644380809761256115058410496352136773475) * 10 ^ 70 +
        9763305728168675270143633678482233161614911576714300820329863442310705) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (120 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_121 :
    recurrence4Scalar2Left.coeff 121 =
      -((((1671834343679970261256493954289627866036023324 * 10 ^ 70 +
        1065490454940813989446492772792064728856515244222898962840868025230900) * 10 ^ 70 +
        6539188337869466846719679437377693994260143320672930741882820853450678) * 10 ^ 70 +
        9440797354145601729160277662513839631565524317705134531954474353284702) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (121 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_122 :
    recurrence4Scalar2Left.coeff 122 =
      ((((12326504098329417682850593809218949630657578148 * 10 ^ 70 +
        0268247508488492355218657731216110189260519721666199395278418661302628) * 10 ^ 70 +
        4967652960287127692837107209947961064878042552840986849354896803899174) * 10 ^ 70 +
        7312172725318837412895240772081894644851825715465131970469916438560944) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (122 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_123 :
    recurrence4Scalar2Left.coeff 123 =
      -((((88951293909064327163032148370731656522909688377 * 10 ^ 70 +
        8404237500187103381485714631377423904706538029667265372458279234345379) * 10 ^ 70 +
        1547156985976740969690688405623725982783106463221397337811169087561423) * 10 ^ 70 +
        2494537582381241123712072821317716069432294220477582452129348900785268) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (123 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_124 :
    recurrence4Scalar2Left.coeff 124 =
      ((((628403092983484682254371547551953660923277013780 * 10 ^ 70 +
        2706357813063086286196624419110645929839463383268941010715517324693312) * 10 ^ 70 +
        3725990250673567413728990425046712746246702168498365827962673833082253) * 10 ^ 70 +
        4821227949436306899435234596872358261667359568946097403205883104318567) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (124 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_125 :
    recurrence4Scalar2Left.coeff 125 =
      -((((4347123071337845784876156454507887046447329432981 * 10 ^ 70 +
        3415178246291737131013333708415480225791067621874561635601892916031192) * 10 ^ 70 +
        7668836033930505121769678621146386497133741831524211639063928069672597) * 10 ^ 70 +
        3291503937883300310336931390060961959054661241615186600489269478071517) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (125 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_126 :
    recurrence4Scalar2Left.coeff 126 =
      ((((29453922929225772487429272185663753291800475665206 * 10 ^ 70 +
        2422936207720011561141402447557914584402648652700128926492282017712471) * 10 ^ 70 +
        8954312924198021545865865303215734138500927426598095961530364238162498) * 10 ^ 70 +
        6214723135062234668497714285586333403131669915508133533879522266968400) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (126 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_127 :
    recurrence4Scalar2Left.coeff 127 =
      -((((195505213916148224841812805806134320542431769755253 * 10 ^ 70 +
        1420103629242591062499963721090631701059716263603512994668954878250143) * 10 ^ 70 +
        7407138952770407990012668724921661996847509703853530803901956254874938) * 10 ^ 70 +
        2597093894545797551783020746793420885051602390402659661937960977868965) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (127 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_128 :
    recurrence4Scalar2Left.coeff 128 =
      ((((1271570790616742627591388851591898987023587556917238 * 10 ^ 70 +
        2391655962115774704619074960945296261103392774722839408667795651322992) * 10 ^ 70 +
        6328009662662639681300157970056510419780965634550175369928269630648510) * 10 ^ 70 +
        5827023014769923559340821837537074110612206872560939578714233633486685) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (128 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_129 :
    recurrence4Scalar2Left.coeff 129 =
      -((((8105495595149272215030722571533973852170745751159998 * 10 ^ 70 +
        6214265492337170526663008658291453084855730317805001297177146688691484) * 10 ^ 70 +
        3480485008519321559476954631009203463053472898171752954799054220151726) * 10 ^ 70 +
        1802586817754539742009283832101517747823763301213720753730410693452308) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (129 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_130 :
    recurrence4Scalar2Left.coeff 130 =
      ((((50647996036585034028720771610512680399990360741385785 * 10 ^ 70 +
        4327780533053345389773319970042925494421377977001306389380734452291148) * 10 ^ 70 +
        3469987281665436237260177281588355421039276898165864966166451176395127) * 10 ^ 70 +
        7811231883955499531407197315353374368203225528322618401661019749248744) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (130 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_131 :
    recurrence4Scalar2Left.coeff 131 =
      -((((310293452747257386911753290985690108950340838343046060 * 10 ^ 70 +
        2591611217051534986127727517107655978713707430785508308374737167862838) * 10 ^ 70 +
        1721304754878967633670505973070025656353733219362124097401686675858343) * 10 ^ 70 +
        5480878710655915228206308230044891120922442628658579006441851407997096) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (131 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_132 :
    recurrence4Scalar2Left.coeff 132 =
      ((((1864197458553413718077863295982934798829493504199008093 * 10 ^ 70 +
        9394216485825542527457296672081996579726249357381857215574113002193961) * 10 ^ 70 +
        9098341133510782104789885360181898859817339838600465420466310686614418) * 10 ^ 70 +
        1338323955472319339843473447156223065615765418887249835379894598117683) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (132 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_133 :
    recurrence4Scalar2Left.coeff 133 =
      -((((10984970869248636197132467490816651298997522538675762169 * 10 ^ 70 +
        2462428129336112938020374874071105108229725587007057119966144721760028) * 10 ^ 70 +
        2344379996829785072648597086207272454116375032035104550376697260746558) * 10 ^ 70 +
        4462826493242827082170326895268332262794704855715341692885390774225146) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (133 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_134 :
    recurrence4Scalar2Left.coeff 134 =
      ((((63499442886525793161255382581175561174724684634545118370 * 10 ^ 70 +
        7550552099447466375269168941415452248783141946921465342619537540918262) * 10 ^ 70 +
        3448535129963064043366767307361558835214164615791261944519362861149988) * 10 ^ 70 +
        0942428988769774357101423329788610226657494438516086262280908281072118) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (134 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_135 :
    recurrence4Scalar2Left.coeff 135 =
      -((((360146262999992154919228008743210327334800628400892566705 * 10 ^ 70 +
        4349512382423762377486088804713867000247973564881241969305741589511242) * 10 ^ 70 +
        8964921072441833562729458970348690976650076470639412913245892252286894) * 10 ^ 70 +
        0576363075028705250611007618460318689650625849977467235136570908204519) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (135 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_136 :
    recurrence4Scalar2Left.coeff 136 =
      ((((2004461250266106584165694408939022962318985530009680293382 * 10 ^ 70 +
        5020099245270384404183481535886649546909734183229538655472067932195275) * 10 ^ 70 +
        9735886215258277550465393265579461077955963201160561977804649908477801) * 10 ^ 70 +
        2800727049383866795125941474463474381346759303476618084902894292115649) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (136 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_137 :
    recurrence4Scalar2Left.coeff 137 =
      -((((10949538244710898340572172157339724417846474551364661145773 * 10 ^ 70 +
        4150111786394570550238066547388002406361668189435870544454330024934842) * 10 ^ 70 +
        2734328195345086215010335847561051718152180813160224633478704242487548) * 10 ^ 70 +
        5751841076692334652896587664599400826201059811274217447266866202595954) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (137 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_138 :
    recurrence4Scalar2Left.coeff 138 =
      ((((58713899114764092086743030057272683040541959025148822208719 * 10 ^ 70 +
        1144011214894347599071314688174917333825156171552906987173306270385118) * 10 ^ 70 +
        8182962520821835275258123051992173888883671600186876703975411627955327) * 10 ^ 70 +
        0621825760655490995855213598064899742335685690971252983775202393081456) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (138 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_139 :
    recurrence4Scalar2Left.coeff 139 =
      -((((309099742912173212677485921258090605568710695772301723498049 * 10 ^ 70 +
        8439125231571453259012190027390080824036633260446621880399664848086026) * 10 ^ 70 +
        2009914511054808379583379011626174363731761209725412369500525156448893) * 10 ^ 70 +
        7471123351057784924387525600182985962604828537366582185441898217893650) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (139 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_140 :
    recurrence4Scalar2Left.coeff 140 =
      ((((1597837856690706888616170903675982113948948657961564544613762 * 10 ^ 70 +
        1463539545488251061800526943516164266041055428810302607849348526070660) * 10 ^ 70 +
        8596298725482403911532648221534699485964774547843758875017614086077124) * 10 ^ 70 +
        9315392330554443830274267541409238665393448035589502513085206776637646) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (140 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_141 :
    recurrence4Scalar2Left.coeff 141 =
      -((((8111571972494959119131233371355446950617528548001648349065006 * 10 ^ 70 +
        5338397561079001436798898392679871418458896700394180470617197679986994) * 10 ^ 70 +
        9917405817054801497429880237453548962794440888093247382254738720996897) * 10 ^ 70 +
        8114350587439404126325915980706130215860535939702382948406090174239863) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (141 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_142 :
    recurrence4Scalar2Left.coeff 142 =
      ((((40446017113073864351187401014817212094899922434260295115023225 * 10 ^ 70 +
        1712660362162048632294651336026376526513455835030301065091273269514725) * 10 ^ 70 +
        4064224618337685964882584251315526513045898739034485994034259518161214) * 10 ^ 70 +
        0504511766335241628383232111625930604243982881498497864098992006833659) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (142 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_143 :
    recurrence4Scalar2Left.coeff 143 =
      -((((198108620659335190423018824756242586095616807415003528563196179 * 10 ^ 70 +
        6053710674843364884635466455869884996286698594026510087362843262277263) * 10 ^ 70 +
        5730470682276527240183452833954306388060813911124368959130464901325627) * 10 ^ 70 +
        0377046131890776661408927507704678282199272661007813269583659648477219) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (143 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_144 :
    recurrence4Scalar2Left.coeff 144 =
      ((((953333129318724619413974475157980486616509576033553717991910104 * 10 ^ 70 +
        2991861689673425573720056343508820183088381936216167152768252571209709) * 10 ^ 70 +
        6623406640574607350260270170170508492104195163143195344060067299560892) * 10 ^ 70 +
        5012959795892093564686039699402869025003004537970674584123136903261148) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (144 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_145 :
    recurrence4Scalar2Left.coeff 145 =
      -((((4507699198509346305723413747235172166035739710804636625341519013 * 10 ^ 70 +
        5685312405247756970338777477845546065081451397962719718930928725429822) * 10 ^ 70 +
        2708789976358149753505178514504828613338006472384486931304592967936160) * 10 ^ 70 +
        0770655858555193503328167482780172173890797465366584753065900898143611) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (145 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_146 :
    recurrence4Scalar2Left.coeff 146 =
      ((((20945358325831401847373328755924782415276543051394150945637114977 * 10 ^ 70 +
        1232632127386749265203421570487334117843426911682042520778806419604590) * 10 ^ 70 +
        2663816282896631573613331668655036191264168238266802142294909659156598) * 10 ^ 70 +
        8886317947040047078129422034546152732517295044853407497472665873923885) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (146 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_147 :
    recurrence4Scalar2Left.coeff 147 =
      -((((95652315670819859062028445501308228987291336500714063366486301465 * 10 ^ 70 +
        8927723207692081783240526526812329415756316245107320308130836626864763) * 10 ^ 70 +
        4319246520338611230998050788603432868574366906714406202186647328333930) * 10 ^ 70 +
        3240293306161838792336813600327205295123794969371077197469742864541879) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (147 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_148 :
    recurrence4Scalar2Left.coeff 148 =
      ((((429367100475386819238044105979047261688475092956973713188689158528 * 10 ^ 70 +
        1671898643952734466855613241286822640315600777792925227773643736573966) * 10 ^ 70 +
        8214124354247543206874304329764901447229628836608788239689374734524457) * 10 ^ 70 +
        1206321647626054751431584678819056536124763020334454800669232752505470) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (148 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_149 :
    recurrence4Scalar2Left.coeff 149 =
      -((((1894684803572332316974706888964989443476476818892057686617775754292 * 10 ^ 70 +
        7350382883575191827641404314296779753305022215405657222775870960144968) * 10 ^ 70 +
        1791971675805717763951284607763058442079230860120918568116716448393221) * 10 ^ 70 +
        6074163041915007360231882263954855113140517908685643325363326918132526) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (149 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_150 :
    recurrence4Scalar2Left.coeff 150 =
      ((((8219929554173120314712397272850209964091368693545323802283211498070 * 10 ^ 70 +
        7069107290089655776726342005550320121160854226820101498708281192160938) * 10 ^ 70 +
        0947508284406015987759938186299484406883923975400449349856152541919428) * 10 ^ 70 +
        8199100826564675213523588131051369943297126157876293150686524451575534) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (150 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_151 :
    recurrence4Scalar2Left.coeff 151 =
      -((((35064592237020586287350110581777386590707276427667556402291192722250 * 10 ^ 70 +
        7769811714083431626147156186238818321740696041967449816403182136862853) * 10 ^ 70 +
        6591620055433077808504537655109087317902446531846511222914795377618002) * 10 ^ 70 +
        0606651730227447900673887712825995462683943597370834073153213214191079) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (151 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_152 :
    recurrence4Scalar2Left.coeff 152 =
      ((((147090434270508235081067927936921093850697645542565282462013192995844 * 10 ^ 70 +
        5903796872027316721649165104042353280866272333123269470934454219799298) * 10 ^ 70 +
        2765778160065540649030406731555285216261973146580971213906873795354508) * 10 ^ 70 +
        6953700691020435196055124250795548501588834796288549198741114346022618) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (152 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_153 :
    recurrence4Scalar2Left.coeff 153 =
      -((((606818926232453240210778347197328327444697762662305977539354237600693 * 10 ^ 70 +
        1498980240130495706953716971337166267562946645040450645814951782464710) * 10 ^ 70 +
        7898921688900611477147216524413067282247490872198861045850521730790145) * 10 ^ 70 +
        5219461655166725084452244752851934449686903306619757706784624261111095) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (153 - x)) = _
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_154 :
    recurrence4Scalar2Left.coeff 154 =
      ((((2462270388979677580578640938064080644728453492571407283490667053883013 * 10 ^ 70 +
        0658521974375277649711133569508376242566872635808161335279951869378436) * 10 ^ 70 +
        0293440762230908452218145515818273163761100840264570632349684986544494) * 10 ^ 70 +
        0116613546670841964730611606038236794230128015869382822508782725793907) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (154 - x)) = _
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
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_155 :
    recurrence4Scalar2Left.coeff 155 =
      -((((9827792985562580650807737913570641238598501082245629778512331016279585 * 10 ^ 70 +
        5982068158416714569185951968060097074517919307000369643329183785252808) * 10 ^ 70 +
        3084323851181614324499436778592381088564239091452662734676331136395373) * 10 ^ 70 +
        2534897070842470068504738751803028003417499918209552599075411642958324) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (155 - x)) = _
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
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_156 :
    recurrence4Scalar2Left.coeff 156 =
      (((((3 * 10 ^ 70 +
        8588724583707045895833244817927684611616113855593981624278647881048532) * 10 ^ 70 +
        5334696112954456797629968785939464413644900620544268351706808888858856) * 10 ^ 70 +
        5378598068448120928732791656697462311171517700321078802864263576873784) * 10 ^ 70 +
        9712425796538891244422714213960546022974424494542436836908328955150923) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (156 - x)) = _
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
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_157 :
    recurrence4Scalar2Left.coeff 157 =
      -(((((14 * 10 ^ 70 +
        9069371210808551903330581384943434085351989415190973717500013843296797) * 10 ^ 70 +
        2288997565728158393166139390638052600242302434961892334750344048167127) * 10 ^ 70 +
        2445112799581751462738044875179101214224612149239158838308085468444192) * 10 ^ 70 +
        6900270348925182357106975984853031578052384169715059545823741240111957) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (157 - x)) = _
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
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_158 :
    recurrence4Scalar2Left.coeff 158 =
      (((((56 * 10 ^ 70 +
        6602234807461048838365660753268266471014958582573746938975051409983092) * 10 ^ 70 +
        9898254968579238437619258742522275674137042661891563682560219285682569) * 10 ^ 70 +
        5538264277288728731734171654495304548211263721955907605458986268352663) * 10 ^ 70 +
        8539396837192802109822972697098380885972314417747581971305328911589608) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (158 - x)) = _
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
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_159 :
    recurrence4Scalar2Left.coeff 159 =
      -(((((211 * 10 ^ 70 +
        9177025983972570504704063482862915856374056525033648803802134727355268) * 10 ^ 70 +
        2189846903037854890532924619139394362305484081755958987791054907502222) * 10 ^ 70 +
        0680033689913571229064580988398628758182677679211237944312823179594920) * 10 ^ 70 +
        2782740530661817696253568239014584171143212051107815361316688361551374) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (159 - x)) = _
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
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_160 :
    recurrence4Scalar2Left.coeff 160 =
      (((((779 * 10 ^ 70 +
        9943414229728036322621805506066282900972847553426712366495439157180994) * 10 ^ 70 +
        4107479593401394896725224084440088509486330931545627454138069546213931) * 10 ^ 70 +
        2971812363958023420281970468996377231683744457698690401623760194356491) * 10 ^ 70 +
        4614026239481282552482175332391461826015403722301442651386163857992681) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (160 - x)) = _
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
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_161 :
    recurrence4Scalar2Left.coeff 161 =
      -(((((2825 * 10 ^ 70 +
        4398891237828200239077468392181884185564867044914646013845312883617644) * 10 ^ 70 +
        0900862486934683779636327592584308883036793297498077221222181201874195) * 10 ^ 70 +
        0747457409892810701348628543244125018778589416460936509223298986564427) * 10 ^ 70 +
        3252171386214804843761048211826580116571376271360478125117736289209604) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (161 - x)) = _
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
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_162 :
    recurrence4Scalar2Left.coeff 162 =
      (((((10073 * 10 ^ 70 +
        6124641270802831583772904501439673377706248652097876613799350657848500) * 10 ^ 70 +
        5835090415163331412498235055007352258928415475946346980500317758864979) * 10 ^ 70 +
        7395067997675806616022332659142282170385619051140248031223647099109911) * 10 ^ 70 +
        0118993174709696072847231411902920936932735158368066470937751201483684) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (162 - x)) = _
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
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_163 :
    recurrence4Scalar2Left.coeff 163 =
      -(((((35352 * 10 ^ 70 +
        6616007439792782837082519888640965759340614436438742466616403693200765) * 10 ^ 70 +
        0011210182429182820149732979660787862766221022041530378112242526163521) * 10 ^ 70 +
        4047373898629213467023317351335924169652295883099607169847199967542493) * 10 ^ 70 +
        7355244758555543131354817777324204643842892846284828299005321191391588) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (163 - x)) = _
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
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_164 :
    recurrence4Scalar2Left.coeff 164 =
      (((((122131 * 10 ^ 70 +
        8421882186051354335206094945947441859703568355761733144416095470023640) * 10 ^ 70 +
        3248308108632928469422604077791895214107079017764014258935346493366172) * 10 ^ 70 +
        4490527793783041138211131616050293764715471251364983591866550552107967) * 10 ^ 70 +
        8689723088772279742687274694410374447482448528721302477593183088846001) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (164 - x)) = _
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
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_165 :
    recurrence4Scalar2Left.coeff 165 =
      -(((((415371 * 10 ^ 70 +
        6808598996206970753704523309469328250340290671090465887013423324163335) * 10 ^ 70 +
        4049044811697322053457391564399809460741637056576194560170579284187682) * 10 ^ 70 +
        9610046987572770507763630446463618924014304975110085748865806474581733) * 10 ^ 70 +
        8806549214200826763146199853377851389479183208352004298772265189327665) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (165 - x)) = _
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
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_166 :
    recurrence4Scalar2Left.coeff 166 =
      (((((1390837 * 10 ^ 70 +
        5214608046898660907391609291141060211717174631329148041946428671091450) * 10 ^ 70 +
        8905421157699629734726849830508079816758170007420615567511445483319890) * 10 ^ 70 +
        5143598775615148118197052363560990255792196845177419715995678322203935) * 10 ^ 70 +
        0190646328201038150210443030435662935739523989960850554956063399659050) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (166 - x)) = _
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
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_167 :
    recurrence4Scalar2Left.coeff 167 =
      -(((((4585396 * 10 ^ 70 +
        6510416368421928858450817088384672226832429489613710023698337749738999) * 10 ^ 70 +
        9345083985989080609833927713290443794124318666165499163163632935630402) * 10 ^ 70 +
        2160818571318678985834265063320263660643471683378616347347791422670420) * 10 ^ 70 +
        6636969795852454388494978074532141348249753170195623728888861201934868) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (167 - x)) = _
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
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_168 :
    recurrence4Scalar2Left.coeff 168 =
      (((((14885622 * 10 ^ 70 +
        4130080461682958391464355822920826526028435390810959551616409783333614) * 10 ^ 70 +
        7666567069083428690848067087111833380155954841390438115388772893647685) * 10 ^ 70 +
        1103820877955763074972904827406697893265399593443329730603522595817751) * 10 ^ 70 +
        1502076954524890744455590954014475460669328311091002523305137383666143) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (168 - x)) = _
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
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_169 :
    recurrence4Scalar2Left.coeff 169 =
      -(((((47585472 * 10 ^ 70 +
        7525031231259433875308113006125022355493825698752652934012537507452535) * 10 ^ 70 +
        3688934449697434308135592764226822911700259737738662837812852385627694) * 10 ^ 70 +
        9911456408980001082194794269149256888654870759241769297268795113259151) * 10 ^ 70 +
        3534648548824913788631863533812002763056465333569328987486321420501881) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (169 - x)) = _
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
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_170 :
    recurrence4Scalar2Left.coeff 170 =
      (((((149804879 * 10 ^ 70 +
        6580156606518226539973157608660353892749229031055061734000694135344872) * 10 ^ 70 +
        8557530488504739440619376657922137403386809873696275093784855818108907) * 10 ^ 70 +
        1303545078644921818696457139445144771662556255282934989528131022289810) * 10 ^ 70 +
        4734884366136699353411052961763314055902251595303579194453102296412757) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (170 - x)) = _
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
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_171 :
    recurrence4Scalar2Left.coeff 171 =
      -(((((464459414 * 10 ^ 70 +
        4389675184267077371446028501900242244017682715732326381392777464233685) * 10 ^ 70 +
        2081444928684278462002296496458956826051764017936054346246509424074807) * 10 ^ 70 +
        0910517109651311099785668201165638194663725054600510857109857672661712) * 10 ^ 70 +
        5848964243448120238754276464607287945973280864792910291902995674382603) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (171 - x)) = _
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
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_172 :
    recurrence4Scalar2Left.coeff 172 =
      (((((1418290084 * 10 ^ 70 +
        5045119954465286382776794275182864393768115586163054331758133054400568) * 10 ^ 70 +
        9073092756869077177994795597438058113197319338095919562799315292226336) * 10 ^ 70 +
        4378271241806574336327538672508589556942641159959916133453277616052684) * 10 ^ 70 +
        2259991371909429822401346665789932395710544221451698834252190719620186) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (172 - x)) = _
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
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_173 :
    recurrence4Scalar2Left.coeff 173 =
      -(((((4265817808 * 10 ^ 70 +
        7861658944269470689717044064153186832376743397390939019195469979017411) * 10 ^ 70 +
        2322942797387734740025640077159359452218264017422320510888427430932378) * 10 ^ 70 +
        9881929543551724821670573283397301072494315444832519245422068245474421) * 10 ^ 70 +
        4811794669302902601764198772709889965333139642165648851343277046002336) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (173 - x)) = _
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
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_174 :
    recurrence4Scalar2Left.coeff 174 =
      (((((12638139755 * 10 ^ 70 +
        4891487460306863203374125591631231424844721896187962189224796825614835) * 10 ^ 70 +
        3036780705436949170974937829305223776238317035877651518356165121993830) * 10 ^ 70 +
        4265452158159563896936201420894092054985585193784370643929539099838715) * 10 ^ 70 +
        3915114805249258960146642571907754286024465875171049127882703114778418) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (174 - x)) = _
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
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_175 :
    recurrence4Scalar2Left.coeff 175 =
      -(((((36883364205 * 10 ^ 70 +
        0390433235303856281258687416133616572545066882472671696203698441027996) * 10 ^ 70 +
        5297062551799263627588027054417982367900133631354267694048042972921633) * 10 ^ 70 +
        4710694620342573851233689704133663093953219348093871985961927875437341) * 10 ^ 70 +
        6691280554381555406687744235325689987280360686337147601155430488840023) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (175 - x)) = _
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
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_176 :
    recurrence4Scalar2Left.coeff 176 =
      (((((106039233308 * 10 ^ 70 +
        1801668450727077561988696852355267887104833623965802319495337016859090) * 10 ^ 70 +
        7111070317188100088697194441095669209579071518257125512804709675706869) * 10 ^ 70 +
        3482734541723016090375445498806640684307508244516521365706425940379028) * 10 ^ 70 +
        6161616286153261867300678769296507999142892742654497394554111452327276) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (176 - x)) = _
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
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_177 :
    recurrence4Scalar2Left.coeff 177 =
      -(((((300339687288 * 10 ^ 70 +
        3100339352170976638508068687216349541696347222792884485541119168961188) * 10 ^ 70 +
        0145568120655604782876186227927208996502906001137898753783529530787907) * 10 ^ 70 +
        7218434908546727687134697183007460696568315579826254944497905810565126) * 10 ^ 70 +
        2103294547369496449143137557201101671643396340084209955537399528654924) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (177 - x)) = _
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
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_178 :
    recurrence4Scalar2Left.coeff 178 =
      (((((838088049676 * 10 ^ 70 +
        6960653288051829836131858913333293030377420738761668145511081798128514) * 10 ^ 70 +
        0711799290094133858468868696036707070332026979597837851423193168242981) * 10 ^ 70 +
        3076432658167346224408185545614955676823977693074501360011856163660050) * 10 ^ 70 +
        9510371267277561083974752712146868865906534602997869971219615713709969) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (178 - x)) = _
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
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_179 :
    recurrence4Scalar2Left.coeff 179 =
      -(((((2304184850638 * 10 ^ 70 +
        7388114614755980921931413542257494806559478893247667196733234468863080) * 10 ^ 70 +
        9788192883041710299504862318108060540352132697521591040009401555285536) * 10 ^ 70 +
        0855801327759580369341459566694568411695927729897181695222281478761506) * 10 ^ 70 +
        0787135835419223462612650313774033578062948107421734295039552704341288) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (179 - x)) = _
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
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_180 :
    recurrence4Scalar2Left.coeff 180 =
      (((((6241873863135 * 10 ^ 70 +
        9695772020518217520477363069605463605358848808820431158601627958573561) * 10 ^ 70 +
        8849778729440670430186887126821175462065325152110471472776135631688361) * 10 ^ 70 +
        1188619899451302420765205018511658409106865852852690196607270639315013) * 10 ^ 70 +
        8072858534861610054337153746553914030687475527120794646000876818269182) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (180 - x)) = _
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
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_181 :
    recurrence4Scalar2Left.coeff 181 =
      -(((((16661005925268 * 10 ^ 70 +
        4604274931627971881616356252655308213165927115704022996609031935619698) * 10 ^ 70 +
        9268998075959981799574916633320096485561364517353994078064108684286680) * 10 ^ 70 +
        8661407386244453607229925611757650292520306188728528994565291083555823) * 10 ^ 70 +
        7708160014198739145086602440312793034404451911480395687415494199012256) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (181 - x)) = _
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
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_182 :
    recurrence4Scalar2Left.coeff 182 =
      (((((43822169501249 * 10 ^ 70 +
        6256594626385258820181063357266558411674925552916176733195131343712045) * 10 ^ 70 +
        2027679663671228470181405120017841275853639560382547514526418520646667) * 10 ^ 70 +
        8054518236155759028703645603483188930305465719314483944509421972241609) * 10 ^ 70 +
        2224288855143786750316762160213854610558715248060818779281791455980209) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (182 - x)) = _
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
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_183 :
    recurrence4Scalar2Left.coeff 183 =
      -(((((113582163107219 * 10 ^ 70 +
        6968318931007580075409845081028362909808622491401416524519307359478521) * 10 ^ 70 +
        2857414989371466189892691148836432370281065621032527798885408739817351) * 10 ^ 70 +
        6206284052951645967225186172411336506885197589073400696656236526557026) * 10 ^ 70 +
        9663241426287184915625374552259729791047717824294584819444405161416462) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (183 - x)) = _
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
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_184 :
    recurrence4Scalar2Left.coeff 184 =
      (((((290112541929000 * 10 ^ 70 +
        1543863206339278677678707446991841973724709619119354897233934666905700) * 10 ^ 70 +
        5040359546187365539718570981123616930996753145043674383615610869919526) * 10 ^ 70 +
        1189415434107932220921849846658759063582724973101925075583516572863071) * 10 ^ 70 +
        0277292996316434749760861674104817651780320271461075406203356277408418) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (184 - x)) = _
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
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_185 :
    recurrence4Scalar2Left.coeff 185 =
      -(((((730262183491797 * 10 ^ 70 +
        5420317713874676626918747180008920400358003301673159836773180740244247) * 10 ^ 70 +
        1646836608805191966982049864578006740049875605171353406607771450636183) * 10 ^ 70 +
        9419105937685423012873043075377991018976671977990555244334391333212707) * 10 ^ 70 +
        9242453767295567069628404988185435502403110043379072835881482689176379) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (185 - x)) = _
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
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Left_coeff_186 :
    recurrence4Scalar2Left.coeff 186 =
      (((((1811599610756624 * 10 ^ 70 +
        3882171581438688885367518253217136046453786494936763194968072070407520) * 10 ^ 70 +
        7299658035227502181547000497698829283107947588719371015138720217671424) * 10 ^ 70 +
        5810784102380175070901969748704096542847266765902117776179899890217692) * 10 ^ 70 +
        8620088429151773409024817095009625239080926800767186232838386161855346) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (186 - x)) = _
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
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (187 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_187 :
    recurrence4Scalar2Left.coeff 187 =
      -(((((4429260511314907 * 10 ^ 70 +
        3921888613912083922424766584194996615695987052191236320130256566323704) * 10 ^ 70 +
        0336807653056114540754290564926777655752585129855835943022903966896688) * 10 ^ 70 +
        0411025301312997626863343134962743617003222660233725058942581728569075) * 10 ^ 70 +
        0261123922245601714219819998995336883008497095597574655737917694700890) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (187 - x)) = _
  rw [show 188 = 1 +
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
  rw [recurrence4Scalar2Left_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (188 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_188 :
    recurrence4Scalar2Left.coeff 188 =
      (((((10673323324514664 * 10 ^ 70 +
        9610320197350452788636172938731884927068565489793556485266021651055176) * 10 ^ 70 +
        1582562317606527943335976575717088452497030535637384025111409360120614) * 10 ^ 70 +
        0739097736945505084820822470595583031846012412316838905514300699693504) * 10 ^ 70 +
        0170154974095162202535692386421715635545083895759249896092184630863339) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (188 - x)) = _
  rw [show 189 = 2 +
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
  rw [recurrence4Scalar2Left_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (189 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_189 :
    recurrence4Scalar2Left.coeff 189 =
      -(((((25350160852196087 * 10 ^ 70 +
        1175471276862741672146065555412335337243872234753900363289743343360475) * 10 ^ 70 +
        1691386667786483543984857539811165697146385309394785810795913975332169) * 10 ^ 70 +
        7478831977385463463302413291112159449184687348888172616038629820584602) * 10 ^ 70 +
        9857020984421708939523874081058281974563280016596053922481528862112033) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (189 - x)) = _
  rw [show 190 = 3 +
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
  rw [recurrence4Scalar2Left_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (190 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_190 :
    recurrence4Scalar2Left.coeff 190 =
      (((((59345378524754538 * 10 ^ 70 +
        5606142198742005212797115135372066813434754864499777654328954422143473) * 10 ^ 70 +
        2716102936826538909947267332163696707203825579498305819706109068137048) * 10 ^ 70 +
        4420642310755533355478390958681936282214159251131261989536162352116292) * 10 ^ 70 +
        7753650833276428614431044328439948584805522376758021696808102411285848) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (190 - x)) = _
  rw [show 191 = 4 +
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
  rw [recurrence4Scalar2Left_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (191 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_191 :
    recurrence4Scalar2Left.coeff 191 =
      -(((((136939923055145526 * 10 ^ 70 +
        2427692991583306979876123138929150451947044068690014097884678271148321) * 10 ^ 70 +
        5183856625259795973967021719703809633049740615999640927688765435398187) * 10 ^ 70 +
        8374125303176151856308955067697039697029478519958463215613695068991172) * 10 ^ 70 +
        0872718775039336723257124261629579685821417028050224232777124481802593) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (191 - x)) = _
  rw [show 192 = 5 +
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
  rw [recurrence4Scalar2Left_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (192 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_192 :
    recurrence4Scalar2Left.coeff 192 =
      (((((311473744170595156 * 10 ^ 70 +
        2688427816357906881628829527928040328908455859659116313678960021207790) * 10 ^ 70 +
        2745242107722619691211596899629775694245847165812008374664757313265306) * 10 ^ 70 +
        0816918767561123387791252722000996679621026865497462150434304396523837) * 10 ^ 70 +
        2730671902797236474261024455054137278346759013301490688248281665170415) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (192 - x)) = _
  rw [show 193 = 6 +
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
  rw [recurrence4Scalar2Left_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (193 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_193 :
    recurrence4Scalar2Left.coeff 193 =
      -(((((698347416559014457 * 10 ^ 70 +
        6375930517575573132893181621394399231800639934895937633869318407243289) * 10 ^ 70 +
        9978750165558514306698264511819436507573391232049770761289171824478963) * 10 ^ 70 +
        9525503259912752602810007380759332306418510691810066251204815299283682) * 10 ^ 70 +
        3016928882408511721663151492150021059062551537677296669797529328337172) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (193 - x)) = _
  rw [show 194 = 7 +
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
  rw [recurrence4Scalar2Left_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (194 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_194 :
    recurrence4Scalar2Left.coeff 194 =
      (((((1543441625258243593 * 10 ^ 70 +
        8015368828489678763701354029784068732112837896471068829155899082771544) * 10 ^ 70 +
        5517561538422550714884814709400990637106806009252737235707617669870451) * 10 ^ 70 +
        8378345012370274646954732647939573197801843241109878142756343513059443) * 10 ^ 70 +
        9727470303791088834372999403003530848679348003471784543390637048514308) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (194 - x)) = _
  rw [show 195 = 8 +
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
  rw [recurrence4Scalar2Left_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (195 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_195 :
    recurrence4Scalar2Left.coeff 195 =
      -(((((3362688745125887768 * 10 ^ 70 +
        2519930330990588597761652550453543594919187374024003099765211844205799) * 10 ^ 70 +
        9690956328021668876794561079266042935724035861870355480053933808406030) * 10 ^ 70 +
        5074499425576431755415322283506588906379093398658590072420322752001602) * 10 ^ 70 +
        5552623372951947125559964757562206832307119531500749822663955329615668) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (195 - x)) = _
  rw [show 196 = 9 +
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
  rw [recurrence4Scalar2Left_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (196 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_196 :
    recurrence4Scalar2Left.coeff 196 =
      (((((7222198643011971138 * 10 ^ 70 +
        2571417563724442550141762778549766927755609023690453194110160522071161) * 10 ^ 70 +
        3341585498895573378654623605256225271817270266412958872808826750869645) * 10 ^ 70 +
        2586399731472222058944665056838288083623675818425391918979790864059228) * 10 ^ 70 +
        6128809931603311714720214005561404123110006902836102477867976461925246) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (196 - x)) = _
  rw [show 197 = 10 +
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
  rw [recurrence4Scalar2Left_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (197 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_197 :
    recurrence4Scalar2Left.coeff 197 =
      -(((((15291366944605894216 * 10 ^ 70 +
        9210293589775570473909932522591983464245826832236447703512408998000883) * 10 ^ 70 +
        2721586470752729521079925377678491120728699574551241795865325215217280) * 10 ^ 70 +
        4493985545673113756979679514922038511164887278319976839861086786116534) * 10 ^ 70 +
        4267457585812561301129834448388921499517348189684987008324621996490491) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (197 - x)) = _
  rw [show 198 = 11 +
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
  rw [recurrence4Scalar2Left_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (198 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_198 :
    recurrence4Scalar2Left.coeff 198 =
      (((((31917174514393117839 * 10 ^ 70 +
        9600944958377307834216176768701135988767587950013521005099266133038070) * 10 ^ 70 +
        9774699497918937568196450118683672311917178741658384340408246944085086) * 10 ^ 70 +
        2996358036267516285098870301753802450583898318298243610565986980171785) * 10 ^ 70 +
        6280437021647228042118048523869365785133532342055345021320864348841295) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (198 - x)) = _
  rw [show 199 = 12 +
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
  rw [recurrence4Scalar2Left_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (199 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_199 :
    recurrence4Scalar2Left.coeff 199 =
      -(((((65676534384883816194 * 10 ^ 70 +
        3501817607527739483383261267022364126374005290685550962300059858818633) * 10 ^ 70 +
        8117155247692798777513655413886622955434277817634114770736485170062999) * 10 ^ 70 +
        5822755060691407240176872666754725178542118223133273164371338529961504) * 10 ^ 70 +
        0758693474366028830051235178510300768058445403073504989540316739174743) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (199 - x)) = _
  rw [show 200 = 13 +
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
  rw [recurrence4Scalar2Left_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (200 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_200 :
    recurrence4Scalar2Left.coeff 200 =
      (((((133232251866107762411 * 10 ^ 70 +
        8351955190591435852397481903026682331072515714111374211428163126573264) * 10 ^ 70 +
        6190484801563346591694936058024309195556870022322810650222264683106577) * 10 ^ 70 +
        4119623696598669009574931060509909242007892907777025858843269877186122) * 10 ^ 70 +
        3610299574573791985323665781045644848884755356405721862757779743087672) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (200 - x)) = _
  rw [show 201 = 14 +
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
  rw [recurrence4Scalar2Left_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (201 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_201 :
    recurrence4Scalar2Left.coeff 201 =
      -(((((266456799638813311269 * 10 ^ 70 +
        0293347069941054555561755590448795418388455304769954378235624161311028) * 10 ^ 70 +
        5076845831426045864613274991666225457639102042060580558057867492105693) * 10 ^ 70 +
        0789674538703977870136750230104269962901248746938624441471137099966964) * 10 ^ 70 +
        7836378511219475383782499298670112356601639971307053854594430863976962) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (201 - x)) = _
  rw [show 202 = 15 +
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
  rw [recurrence4Scalar2Left_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (202 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_202 :
    recurrence4Scalar2Left.coeff 202 =
      (((((525371770191442326870 * 10 ^ 70 +
        2017269461715106607006827557054054426708740544912297935867967166247054) * 10 ^ 70 +
        5169942552134592403371383504398489406197767965876482337391421842895664) * 10 ^ 70 +
        8323435849986544192832682380081706413117794040609595196208151941056637) * 10 ^ 70 +
        6533191980611348523581251368178512982696064730073898770906904329375207) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (202 - x)) = _
  rw [show 203 = 16 +
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
  rw [recurrence4Scalar2Left_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (203 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_203 :
    recurrence4Scalar2Left.coeff 203 =
      -(((((1021251136765573429480 * 10 ^ 70 +
        6840729894796334058280883640549626098707154060391969224563766388082110) * 10 ^ 70 +
        5487993575623988871379813296317349857953876888206282258109449038168085) * 10 ^ 70 +
        3908343443566787016447399007104858566626261995098997970308444530199489) * 10 ^ 70 +
        4441649120141235413561576860378668072626975240894837358006189315113795) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (203 - x)) = _
  rw [show 204 = 17 +
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
  rw [recurrence4Scalar2Left_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (204 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_204 :
    recurrence4Scalar2Left.coeff 204 =
      (((((1957162426924418915784 * 10 ^ 70 +
        6347506670587511284046881903604314325672977084939196529179860104598910) * 10 ^ 70 +
        6110688544095326421947837217650011102215860481519571078206421289173959) * 10 ^ 70 +
        1775771976083678772589094224370482015769435839859096563955949246769720) * 10 ^ 70 +
        3471247872052128298428031513910647571149430728045504982808293010605776) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (204 - x)) = _
  rw [show 205 = 18 +
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
  rw [recurrence4Scalar2Left_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (205 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_205 :
    recurrence4Scalar2Left.coeff 205 =
      -(((((3697868429711283940374 * 10 ^ 70 +
        2456267064609342831572552977104961870564085577667929582800250513407539) * 10 ^ 70 +
        9430746430918007192952487673893872370467014377031903012007818417334469) * 10 ^ 70 +
        7020502015078900503934832684662420736830955700561971421877389357073540) * 10 ^ 70 +
        0576355993545131233301807809355954244818955622110496541647031823591306) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (205 - x)) = _
  rw [show 206 = 19 +
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
  rw [recurrence4Scalar2Left_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (206 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_206 :
    recurrence4Scalar2Left.coeff 206 =
      (((((6888223317773582821223 * 10 ^ 70 +
        7555864636444457153671985500142090532179998378403887903189055021218101) * 10 ^ 70 +
        2353157828261523673381623779806221435665275487723133400887466781635485) * 10 ^ 70 +
        0282832946075289449759709617124130923528595767896348337236442410887302) * 10 ^ 70 +
        8218436128823193431255991456957492723005889794810016858639073639025691) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (206 - x)) = _
  rw [show 207 = 20 +
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
  rw [recurrence4Scalar2Left_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (207 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_207 :
    recurrence4Scalar2Left.coeff 207 =
      -(((((12650106319834758164389 * 10 ^ 70 +
        5020129499803051622015829745891103478786703442538376138173924731006737) * 10 ^ 70 +
        4214178935150752903981975607233252100785980969962251702585537940931789) * 10 ^ 70 +
        8448376601392162031838211569788023203295415608847449480382371794726929) * 10 ^ 70 +
        9735687308007239354009029073705284064971031496865643946754610082301708) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (207 - x)) = _
  rw [show 208 = 21 +
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
  rw [recurrence4Scalar2Left_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (208 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_208 :
    recurrence4Scalar2Left.coeff 208 =
      (((((22904003820542290947070 * 10 ^ 70 +
        4252043709483417545167421684671637291012335862898687836143391626921396) * 10 ^ 70 +
        4686940325951464244997544038977805772997547734291188451849854513498917) * 10 ^ 70 +
        3785061423705111316634803044004421206645205716289042048142598669155537) * 10 ^ 70 +
        8981997159896224122679545654976188760609736989560958116590420128120951) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (208 - x)) = _
  rw [show 209 = 22 +
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
  rw [recurrence4Scalar2Left_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (209 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_209 :
    recurrence4Scalar2Left.coeff 209 =
      -(((((40884342679984804845390 * 10 ^ 70 +
        5126950420867638659100122232338025437396755318135570249289300275062836) * 10 ^ 70 +
        9062086373055067058923224742987887811219686365393196829464868336473506) * 10 ^ 70 +
        5059845090218008272866348748786821417388646382269986775719170823511887) * 10 ^ 70 +
        1810202352531287483820827855761645149773223259721789062246798729444034) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (209 - x)) = _
  rw [show 210 = 23 +
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
  rw [recurrence4Scalar2Left_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (210 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_210 :
    recurrence4Scalar2Left.coeff 210 =
      (((((71949552087118721235762 * 10 ^ 70 +
        1142223055440623136113838446644536079396359714265374552272560093101280) * 10 ^ 70 +
        3057238272131854500073690389167155178810767705887639026427700908575833) * 10 ^ 70 +
        0066359601046144625964025233647743449869736326766375680584241823209414) * 10 ^ 70 +
        4206159529160964932670175348775737762869298994829767231800217667231895) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (210 - x)) = _
  rw [show 211 = 24 +
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
  rw [recurrence4Scalar2Left_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (211 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_211 :
    recurrence4Scalar2Left.coeff 211 =
      -(((((124830479071582926584922 * 10 ^ 70 +
        6677705122540710508939866069714083680536831483404802208912393157158844) * 10 ^ 70 +
        7934518036073321699128713291966948343333934989071399617516971706904155) * 10 ^ 70 +
        7774132783152434933882358133146222703646052219484366064614397484060449) * 10 ^ 70 +
        4216955446432799962493877640014754880726674921065109068680830848816632) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (211 - x)) = _
  rw [show 212 = 25 +
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
  rw [recurrence4Scalar2Left_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (212 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_212 :
    recurrence4Scalar2Left.coeff 212 =
      (((((213515553102202429493131 * 10 ^ 70 +
        6808578771851564671587793086023264662490735736382874302575114136852213) * 10 ^ 70 +
        4624890134103045773234163238374647605044563725260110906288302092750209) * 10 ^ 70 +
        6675732749508025745260141357755923482925976191488842564435011412997042) * 10 ^ 70 +
        7769763033775763514334478235140110717789934290901294568224221145541957) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (212 - x)) = _
  rw [show 213 = 26 +
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
  rw [recurrence4Scalar2Left_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (213 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_213 :
    recurrence4Scalar2Left.coeff 213 =
      -(((((360038044651331041688748 * 10 ^ 70 +
        3576618582684189557276431501112653334193966684450635104468460623872113) * 10 ^ 70 +
        3778313593337850075790727818328432041737231157160145792605009628895924) * 10 ^ 70 +
        0306672484480448150772443692145809173886443713674700293879433538191601) * 10 ^ 70 +
        4296412737757535441832534575710947116071252592157430268684645554333416) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (213 - x)) = _
  rw [show 214 = 27 +
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
  rw [recurrence4Scalar2Left_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (214 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_214 :
    recurrence4Scalar2Left.coeff 214 =
      (((((598507583292484760759001 * 10 ^ 70 +
        0810574286000177992153159998162866546603470381348600064045573539121531) * 10 ^ 70 +
        2491317119919572786786244360529051458119329209122662634373057728401475) * 10 ^ 70 +
        1394928504646126184205690719552705097867952038317691136627077653969650) * 10 ^ 70 +
        0475897787478196456958805064924135826060007643421902437877506135133664) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (214 - x)) = _
  rw [show 215 = 28 +
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
  rw [recurrence4Scalar2Left_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (215 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_215 :
    recurrence4Scalar2Left.coeff 215 =
      -(((((980808734173009228714100 * 10 ^ 70 +
        1244310734067934883951991066977152038967435353247297066672800128382409) * 10 ^ 70 +
        7944761755156529063585650415969246512003546026182957361228619069603286) * 10 ^ 70 +
        8749479735227821353453961693113490674351700088949670025209130028855338) * 10 ^ 70 +
        0418238817085921061908788332932743407864374811600948848289774058087837) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (215 - x)) = _
  rw [show 216 = 29 +
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
  rw [recurrence4Scalar2Left_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (216 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_216 :
    recurrence4Scalar2Left.coeff 216 =
      (((((1584462464147224873363107 * 10 ^ 70 +
        5809371828101830725080321159519351485332099703943378333399432930367216) * 10 ^ 70 +
        6222264696307430211266642813719251070035954603825801126400843589693049) * 10 ^ 70 +
        5307485208218400357093939332246170190971789565058657416929657157549031) * 10 ^ 70 +
        1092483377247335473902325338830984240715492860592402046669384917299272) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (216 - x)) = _
  rw [show 217 = 30 +
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
  rw [recurrence4Scalar2Left_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (217 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_217 :
    recurrence4Scalar2Left.coeff 217 =
      -(((((2523193400019450058073365 * 10 ^ 70 +
        7081499619657452023198777323326332122654169260268234808929601148730716) * 10 ^ 70 +
        3081120174526963802239387356151322862726385354554458256413863603297639) * 10 ^ 70 +
        2291943193053523651723026057280738276218059932995593460012410334996691) * 10 ^ 70 +
        6544228143361682094887049623750376622263965804078026291234224563900461) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (217 - x)) = _
  rw [show 218 = 31 +
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
  rw [recurrence4Scalar2Left_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (218 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_218 :
    recurrence4Scalar2Left.coeff 218 =
      (((((3960740404063766048446010 * 10 ^ 70 +
        1474745191564937727658364500220017910053524699921215258609031382937757) * 10 ^ 70 +
        6907003469782198207115178942918397100385048225867760672988234333956471) * 10 ^ 70 +
        5237045548432195067625685684319661713168253295833407809437444231408410) * 10 ^ 70 +
        9642099202952675382776661516727150346730559446876230994760454390004141) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (218 - x)) = _
  rw [show 219 = 32 +
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
  rw [recurrence4Scalar2Left_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (219 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_219 :
    recurrence4Scalar2Left.coeff 219 =
      -(((((6128355373115508369633805 * 10 ^ 70 +
        9297028593672219591880921616903340842944175792757597670154364276500184) * 10 ^ 70 +
        9867272944301920817018603789162587658326869993781054532333947140597846) * 10 ^ 70 +
        7547426279768899106296050525958899327164424175545676829433877967660156) * 10 ^ 70 +
        7539494113271329427850475990116344627526590353126223753522453788423091) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (219 - x)) = _
  rw [show 220 = 33 +
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
  rw [recurrence4Scalar2Left_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (220 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_220 :
    recurrence4Scalar2Left.coeff 220 =
      (((((9346213776150305779465312 * 10 ^ 70 +
        7531609384744737685805777686298846652363509385730111045508340820625045) * 10 ^ 70 +
        6047226515600139118766918198673331320598201755455509779264663196843638) * 10 ^ 70 +
        7176485058142457510830718579487964706342685451092543362306828891282120) * 10 ^ 70 +
        9678711114484802301490510064749941316932383512512970384615805917709401) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (220 - x)) = _
  rw [show 221 = 34 +
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
  rw [recurrence4Scalar2Left_coeff_220_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (221 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_221 :
    recurrence4Scalar2Left.coeff 221 =
      -(((((14048566140220743025274664 * 10 ^ 70 +
        8817191899767434919674887777190807406431939771178851624720319483606453) * 10 ^ 70 +
        7412603228198348676066040954525616538921437924411178636897901995095997) * 10 ^ 70 +
        0553104451409501967708483553841425557327655723922599953140841637707883) * 10 ^ 70 +
        4900756003018303047747469368242639130710156063138183542260826700743779) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (221 - x)) = _
  rw [show 222 = 35 +
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
  rw [recurrence4Scalar2Left_coeff_221_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (222 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_222 :
    recurrence4Scalar2Left.coeff 222 =
      (((((20811853109689536044461476 * 10 ^ 70 +
        5698767483260898984556030632964373332971582150742682731166289150093790) * 10 ^ 70 +
        0293688629606655393665163388700491626743141021876624405330692302793202) * 10 ^ 70 +
        0744235073161658761721456555177028904412164708292082733524845124335766) * 10 ^ 70 +
        5757195072593008042514727906254453887833204659166426590194059217122250) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (222 - x)) = _
  rw [show 223 = 36 +
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
  rw [recurrence4Scalar2Left_coeff_222_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A2_coeff_high (223 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Left_coeff_223 :
    recurrence4Scalar2Left.coeff 223 =
      -(((((30384164210308966712866578 * 10 ^ 70 +
        3612497719086240818950200391102334432837256660368032952314560124805571) * 10 ^ 70 +
        5818903268003948144067947972317812155744901911289875252339028763576943) * 10 ^ 70 +
        9725884558126811052367741985074590195429355454871364051386776987647611) * 10 ^ 70 +
        5328476137295921689918627612621035132644756834512730888374120251271457) : ℚ) := by
  unfold recurrence4Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient2.coeff (223 - x)) = _
  rw [show 224 = 37 +
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
  rw [recurrence4Scalar2Left_coeff_223_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
