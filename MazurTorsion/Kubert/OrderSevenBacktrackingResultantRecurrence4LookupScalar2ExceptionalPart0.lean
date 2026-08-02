/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC2
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C2_coeff_0
  recurrence4C2_coeff_1
  recurrence4C2_coeff_10
  recurrence4C2_coeff_100
  recurrence4C2_coeff_101
  recurrence4C2_coeff_102
  recurrence4C2_coeff_103
  recurrence4C2_coeff_104
  recurrence4C2_coeff_105
  recurrence4C2_coeff_106
  recurrence4C2_coeff_107
  recurrence4C2_coeff_108
  recurrence4C2_coeff_109
  recurrence4C2_coeff_11
  recurrence4C2_coeff_110
  recurrence4C2_coeff_111
  recurrence4C2_coeff_112
  recurrence4C2_coeff_113
  recurrence4C2_coeff_114
  recurrence4C2_coeff_115
  recurrence4C2_coeff_116
  recurrence4C2_coeff_117
  recurrence4C2_coeff_118
  recurrence4C2_coeff_119
  recurrence4C2_coeff_12
  recurrence4C2_coeff_120
  recurrence4C2_coeff_121
  recurrence4C2_coeff_122
  recurrence4C2_coeff_123
  recurrence4C2_coeff_124
  recurrence4C2_coeff_125
  recurrence4C2_coeff_126
  recurrence4C2_coeff_127
  recurrence4C2_coeff_128
  recurrence4C2_coeff_129
  recurrence4C2_coeff_13
  recurrence4C2_coeff_130
  recurrence4C2_coeff_131
  recurrence4C2_coeff_132
  recurrence4C2_coeff_133
  recurrence4C2_coeff_134
  recurrence4C2_coeff_135
  recurrence4C2_coeff_136
  recurrence4C2_coeff_137
  recurrence4C2_coeff_138
  recurrence4C2_coeff_139
  recurrence4C2_coeff_14
  recurrence4C2_coeff_140
  recurrence4C2_coeff_141
  recurrence4C2_coeff_142
  recurrence4C2_coeff_143
  recurrence4C2_coeff_144
  recurrence4C2_coeff_145
  recurrence4C2_coeff_15
  recurrence4C2_coeff_16
  recurrence4C2_coeff_17
  recurrence4C2_coeff_18
  recurrence4C2_coeff_19
  recurrence4C2_coeff_2
  recurrence4C2_coeff_20
  recurrence4C2_coeff_21
  recurrence4C2_coeff_22
  recurrence4C2_coeff_23
  recurrence4C2_coeff_24

attribute [local simp]
  recurrence4C2_coeff_25
  recurrence4C2_coeff_26
  recurrence4C2_coeff_27
  recurrence4C2_coeff_28
  recurrence4C2_coeff_29
  recurrence4C2_coeff_3
  recurrence4C2_coeff_30
  recurrence4C2_coeff_31
  recurrence4C2_coeff_32
  recurrence4C2_coeff_33
  recurrence4C2_coeff_34
  recurrence4C2_coeff_35
  recurrence4C2_coeff_36
  recurrence4C2_coeff_37
  recurrence4C2_coeff_38
  recurrence4C2_coeff_39
  recurrence4C2_coeff_4
  recurrence4C2_coeff_40
  recurrence4C2_coeff_41
  recurrence4C2_coeff_42
  recurrence4C2_coeff_43
  recurrence4C2_coeff_44
  recurrence4C2_coeff_45
  recurrence4C2_coeff_46
  recurrence4C2_coeff_47
  recurrence4C2_coeff_48
  recurrence4C2_coeff_49
  recurrence4C2_coeff_5
  recurrence4C2_coeff_50
  recurrence4C2_coeff_51
  recurrence4C2_coeff_52
  recurrence4C2_coeff_53
  recurrence4C2_coeff_54
  recurrence4C2_coeff_55
  recurrence4C2_coeff_56
  recurrence4C2_coeff_57
  recurrence4C2_coeff_58
  recurrence4C2_coeff_59
  recurrence4C2_coeff_6
  recurrence4C2_coeff_60
  recurrence4C2_coeff_61
  recurrence4C2_coeff_62
  recurrence4C2_coeff_63
  recurrence4C2_coeff_64
  recurrence4C2_coeff_65
  recurrence4C2_coeff_66
  recurrence4C2_coeff_67
  recurrence4C2_coeff_68
  recurrence4C2_coeff_69
  recurrence4C2_coeff_7
  recurrence4C2_coeff_70
  recurrence4C2_coeff_71
  recurrence4C2_coeff_72
  recurrence4C2_coeff_73
  recurrence4C2_coeff_74
  recurrence4C2_coeff_75
  recurrence4C2_coeff_76
  recurrence4C2_coeff_77
  recurrence4C2_coeff_78
  recurrence4C2_coeff_79
  recurrence4C2_coeff_8
  recurrence4C2_coeff_80
  recurrence4C2_coeff_81
  recurrence4C2_coeff_82

attribute [local simp]
  recurrence4C2_coeff_83
  recurrence4C2_coeff_84
  recurrence4C2_coeff_85
  recurrence4C2_coeff_86
  recurrence4C2_coeff_87
  recurrence4C2_coeff_88
  recurrence4C2_coeff_89
  recurrence4C2_coeff_9
  recurrence4C2_coeff_90
  recurrence4C2_coeff_91
  recurrence4C2_coeff_92
  recurrence4C2_coeff_93
  recurrence4C2_coeff_94
  recurrence4C2_coeff_95
  recurrence4C2_coeff_96
  recurrence4C2_coeff_97
  recurrence4C2_coeff_98
  recurrence4C2_coeff_99
  recurrence4ExceptionalProduct_coeff_0
  recurrence4ExceptionalProduct_coeff_1
  recurrence4ExceptionalProduct_coeff_10
  recurrence4ExceptionalProduct_coeff_100
  recurrence4ExceptionalProduct_coeff_101
  recurrence4ExceptionalProduct_coeff_102
  recurrence4ExceptionalProduct_coeff_103
  recurrence4ExceptionalProduct_coeff_104
  recurrence4ExceptionalProduct_coeff_105
  recurrence4ExceptionalProduct_coeff_106
  recurrence4ExceptionalProduct_coeff_107
  recurrence4ExceptionalProduct_coeff_108
  recurrence4ExceptionalProduct_coeff_109
  recurrence4ExceptionalProduct_coeff_11
  recurrence4ExceptionalProduct_coeff_110
  recurrence4ExceptionalProduct_coeff_111
  recurrence4ExceptionalProduct_coeff_112
  recurrence4ExceptionalProduct_coeff_113
  recurrence4ExceptionalProduct_coeff_114
  recurrence4ExceptionalProduct_coeff_115
  recurrence4ExceptionalProduct_coeff_116
  recurrence4ExceptionalProduct_coeff_117
  recurrence4ExceptionalProduct_coeff_118
  recurrence4ExceptionalProduct_coeff_119
  recurrence4ExceptionalProduct_coeff_12
  recurrence4ExceptionalProduct_coeff_120
  recurrence4ExceptionalProduct_coeff_121
  recurrence4ExceptionalProduct_coeff_122
  recurrence4ExceptionalProduct_coeff_123
  recurrence4ExceptionalProduct_coeff_124
  recurrence4ExceptionalProduct_coeff_125
  recurrence4ExceptionalProduct_coeff_126
  recurrence4ExceptionalProduct_coeff_127
  recurrence4ExceptionalProduct_coeff_128
  recurrence4ExceptionalProduct_coeff_129
  recurrence4ExceptionalProduct_coeff_13
  recurrence4ExceptionalProduct_coeff_130
  recurrence4ExceptionalProduct_coeff_131
  recurrence4ExceptionalProduct_coeff_132
  recurrence4ExceptionalProduct_coeff_133
  recurrence4ExceptionalProduct_coeff_134
  recurrence4ExceptionalProduct_coeff_135
  recurrence4ExceptionalProduct_coeff_136
  recurrence4ExceptionalProduct_coeff_137
  recurrence4ExceptionalProduct_coeff_138
  recurrence4ExceptionalProduct_coeff_139

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_14
  recurrence4ExceptionalProduct_coeff_140
  recurrence4ExceptionalProduct_coeff_141
  recurrence4ExceptionalProduct_coeff_142
  recurrence4ExceptionalProduct_coeff_143
  recurrence4ExceptionalProduct_coeff_144
  recurrence4ExceptionalProduct_coeff_145
  recurrence4ExceptionalProduct_coeff_146
  recurrence4ExceptionalProduct_coeff_147
  recurrence4ExceptionalProduct_coeff_148
  recurrence4ExceptionalProduct_coeff_149
  recurrence4ExceptionalProduct_coeff_15
  recurrence4ExceptionalProduct_coeff_150
  recurrence4ExceptionalProduct_coeff_151
  recurrence4ExceptionalProduct_coeff_152
  recurrence4ExceptionalProduct_coeff_153
  recurrence4ExceptionalProduct_coeff_154
  recurrence4ExceptionalProduct_coeff_155
  recurrence4ExceptionalProduct_coeff_156
  recurrence4ExceptionalProduct_coeff_157
  recurrence4ExceptionalProduct_coeff_158
  recurrence4ExceptionalProduct_coeff_159
  recurrence4ExceptionalProduct_coeff_16
  recurrence4ExceptionalProduct_coeff_160
  recurrence4ExceptionalProduct_coeff_161
  recurrence4ExceptionalProduct_coeff_162
  recurrence4ExceptionalProduct_coeff_163
  recurrence4ExceptionalProduct_coeff_164
  recurrence4ExceptionalProduct_coeff_165
  recurrence4ExceptionalProduct_coeff_166
  recurrence4ExceptionalProduct_coeff_167
  recurrence4ExceptionalProduct_coeff_168
  recurrence4ExceptionalProduct_coeff_169
  recurrence4ExceptionalProduct_coeff_17
  recurrence4ExceptionalProduct_coeff_170
  recurrence4ExceptionalProduct_coeff_171
  recurrence4ExceptionalProduct_coeff_172
  recurrence4ExceptionalProduct_coeff_173
  recurrence4ExceptionalProduct_coeff_174
  recurrence4ExceptionalProduct_coeff_175
  recurrence4ExceptionalProduct_coeff_176
  recurrence4ExceptionalProduct_coeff_177
  recurrence4ExceptionalProduct_coeff_178
  recurrence4ExceptionalProduct_coeff_179
  recurrence4ExceptionalProduct_coeff_18
  recurrence4ExceptionalProduct_coeff_180
  recurrence4ExceptionalProduct_coeff_181
  recurrence4ExceptionalProduct_coeff_182
  recurrence4ExceptionalProduct_coeff_183
  recurrence4ExceptionalProduct_coeff_184
  recurrence4ExceptionalProduct_coeff_185
  recurrence4ExceptionalProduct_coeff_186
  recurrence4ExceptionalProduct_coeff_187
  recurrence4ExceptionalProduct_coeff_188
  recurrence4ExceptionalProduct_coeff_189
  recurrence4ExceptionalProduct_coeff_19
  recurrence4ExceptionalProduct_coeff_190
  recurrence4ExceptionalProduct_coeff_191
  recurrence4ExceptionalProduct_coeff_192
  recurrence4ExceptionalProduct_coeff_193
  recurrence4ExceptionalProduct_coeff_194
  recurrence4ExceptionalProduct_coeff_195
  recurrence4ExceptionalProduct_coeff_196
  recurrence4ExceptionalProduct_coeff_197

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_198
  recurrence4ExceptionalProduct_coeff_199
  recurrence4ExceptionalProduct_coeff_2
  recurrence4ExceptionalProduct_coeff_20
  recurrence4ExceptionalProduct_coeff_200
  recurrence4ExceptionalProduct_coeff_201
  recurrence4ExceptionalProduct_coeff_202
  recurrence4ExceptionalProduct_coeff_203
  recurrence4ExceptionalProduct_coeff_204
  recurrence4ExceptionalProduct_coeff_205
  recurrence4ExceptionalProduct_coeff_206
  recurrence4ExceptionalProduct_coeff_207
  recurrence4ExceptionalProduct_coeff_208
  recurrence4ExceptionalProduct_coeff_209
  recurrence4ExceptionalProduct_coeff_21
  recurrence4ExceptionalProduct_coeff_210
  recurrence4ExceptionalProduct_coeff_211
  recurrence4ExceptionalProduct_coeff_212
  recurrence4ExceptionalProduct_coeff_213
  recurrence4ExceptionalProduct_coeff_214
  recurrence4ExceptionalProduct_coeff_215
  recurrence4ExceptionalProduct_coeff_216
  recurrence4ExceptionalProduct_coeff_217
  recurrence4ExceptionalProduct_coeff_218
  recurrence4ExceptionalProduct_coeff_219
  recurrence4ExceptionalProduct_coeff_22
  recurrence4ExceptionalProduct_coeff_23
  recurrence4ExceptionalProduct_coeff_24
  recurrence4ExceptionalProduct_coeff_25
  recurrence4ExceptionalProduct_coeff_26
  recurrence4ExceptionalProduct_coeff_27
  recurrence4ExceptionalProduct_coeff_28
  recurrence4ExceptionalProduct_coeff_29
  recurrence4ExceptionalProduct_coeff_3
  recurrence4ExceptionalProduct_coeff_30
  recurrence4ExceptionalProduct_coeff_31
  recurrence4ExceptionalProduct_coeff_32
  recurrence4ExceptionalProduct_coeff_33
  recurrence4ExceptionalProduct_coeff_34
  recurrence4ExceptionalProduct_coeff_35
  recurrence4ExceptionalProduct_coeff_36
  recurrence4ExceptionalProduct_coeff_37
  recurrence4ExceptionalProduct_coeff_38
  recurrence4ExceptionalProduct_coeff_39
  recurrence4ExceptionalProduct_coeff_4
  recurrence4ExceptionalProduct_coeff_40
  recurrence4ExceptionalProduct_coeff_41
  recurrence4ExceptionalProduct_coeff_42
  recurrence4ExceptionalProduct_coeff_43
  recurrence4ExceptionalProduct_coeff_44
  recurrence4ExceptionalProduct_coeff_45
  recurrence4ExceptionalProduct_coeff_46
  recurrence4ExceptionalProduct_coeff_47
  recurrence4ExceptionalProduct_coeff_48
  recurrence4ExceptionalProduct_coeff_49
  recurrence4ExceptionalProduct_coeff_5
  recurrence4ExceptionalProduct_coeff_50
  recurrence4ExceptionalProduct_coeff_51
  recurrence4ExceptionalProduct_coeff_52
  recurrence4ExceptionalProduct_coeff_53
  recurrence4ExceptionalProduct_coeff_54
  recurrence4ExceptionalProduct_coeff_55
  recurrence4ExceptionalProduct_coeff_56
  recurrence4ExceptionalProduct_coeff_57

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_58
  recurrence4ExceptionalProduct_coeff_59
  recurrence4ExceptionalProduct_coeff_6
  recurrence4ExceptionalProduct_coeff_60
  recurrence4ExceptionalProduct_coeff_61
  recurrence4ExceptionalProduct_coeff_62
  recurrence4ExceptionalProduct_coeff_63
  recurrence4ExceptionalProduct_coeff_64
  recurrence4ExceptionalProduct_coeff_65
  recurrence4ExceptionalProduct_coeff_66
  recurrence4ExceptionalProduct_coeff_67
  recurrence4ExceptionalProduct_coeff_68
  recurrence4ExceptionalProduct_coeff_69
  recurrence4ExceptionalProduct_coeff_7
  recurrence4ExceptionalProduct_coeff_70
  recurrence4ExceptionalProduct_coeff_71
  recurrence4ExceptionalProduct_coeff_72
  recurrence4ExceptionalProduct_coeff_73
  recurrence4ExceptionalProduct_coeff_74
  recurrence4ExceptionalProduct_coeff_75
  recurrence4ExceptionalProduct_coeff_76
  recurrence4ExceptionalProduct_coeff_77
  recurrence4ExceptionalProduct_coeff_78
  recurrence4ExceptionalProduct_coeff_79
  recurrence4ExceptionalProduct_coeff_8
  recurrence4ExceptionalProduct_coeff_80
  recurrence4ExceptionalProduct_coeff_81
  recurrence4ExceptionalProduct_coeff_82
  recurrence4ExceptionalProduct_coeff_83
  recurrence4ExceptionalProduct_coeff_84
  recurrence4ExceptionalProduct_coeff_85
  recurrence4ExceptionalProduct_coeff_86
  recurrence4ExceptionalProduct_coeff_87
  recurrence4ExceptionalProduct_coeff_88
  recurrence4ExceptionalProduct_coeff_89
  recurrence4ExceptionalProduct_coeff_9
  recurrence4ExceptionalProduct_coeff_90
  recurrence4ExceptionalProduct_coeff_91
  recurrence4ExceptionalProduct_coeff_92
  recurrence4ExceptionalProduct_coeff_93
  recurrence4ExceptionalProduct_coeff_94
  recurrence4ExceptionalProduct_coeff_95
  recurrence4ExceptionalProduct_coeff_96
  recurrence4ExceptionalProduct_coeff_97
  recurrence4ExceptionalProduct_coeff_98
  recurrence4ExceptionalProduct_coeff_99

theorem recurrence4Scalar2Exceptional_coeff_0 :
    recurrence4Scalar2Exceptional.coeff 0 =
      (-69361034541562778333826486175232717553664 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 1,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (0 - x)) = _
  rw [show 1 = 0 +
    1 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 1 = 1 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_1 :
    recurrence4Scalar2Exceptional.coeff 1 =
      (144485167788367069654875209596710129798508544 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 2,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (1 - x)) = _
  rw [show 2 = 0 +
    2 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 2 = 2 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_2 :
    recurrence4Scalar2Exceptional.coeff 2 =
      (-341109060376047963898306476498344830103525431296 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 3,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (2 - x)) = _
  rw [show 3 = 0 +
    3 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 3 = 3 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_3 :
    recurrence4Scalar2Exceptional.coeff 3 =
      (2281041944934565862941280324194209967140422824971456 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 4,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (3 - x)) = _
  rw [show 4 = 0 +
    4 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 4 = 4 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_4 :
    recurrence4Scalar2Exceptional.coeff 4 =
      (-2735462438149741027363594108725632788960763266996715200 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 5,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (4 - x)) = _
  rw [show 5 = 0 +
    5 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 5 = 5 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_5 :
    recurrence4Scalar2Exceptional.coeff 5 =
      (-6140819563599904639765122476541955345805598000196060646928 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 6,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (5 - x)) = _
  rw [show 6 = 0 +
    6 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 6 = 6 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_6 :
    recurrence4Scalar2Exceptional.coeff 6 =
      (15111796492310470556814667908422467010238626153069528535766752 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 7,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (6 - x)) = _
  rw [show 7 = 0 +
    7 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_7 :
    recurrence4Scalar2Exceptional.coeff 7 =
      (-8708678871658187236050490209106493017708052233089413418064510976 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 8,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (7 - x)) = _
  rw [show 8 = 0 +
    8 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 8 = 8 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_8 :
    recurrence4Scalar2Exceptional.coeff 8 =
      (-8366870363267876614910735236263640829781650733598963541334382830448 : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 9,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (8 - x)) = _
  rw [show 9 = 0 +
    9 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 9 = 9 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_9 :
    recurrence4Scalar2Exceptional.coeff 9 =
      ((1 * 10 ^ 70 +
        8916467388002539141167137050344503305328954646300573060990461073453196) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 10,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (9 - x)) = _
  rw [show 10 = 0 +
    10 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 10 = 10 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_10 :
    recurrence4Scalar2Exceptional.coeff 10 =
      -((1528 * 10 ^ 70 +
        6496382481785416281879935118230830309332764215567757694745516298907704) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 11,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (10 - x)) = _
  rw [show 11 = 0 +
    11 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_11 :
    recurrence4Scalar2Exceptional.coeff 11 =
      ((548881 * 10 ^ 70 +
        5302616610260433858327421040214116058075013153907246896879504861738368) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 12,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (11 - x)) = _
  rw [show 12 = 0 +
    12 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_12 :
    recurrence4Scalar2Exceptional.coeff 12 =
      ((63459985 * 10 ^ 70 +
        1745054791023694616455133815118422407635292257702739678339655579660440) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 13,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (12 - x)) = _
  rw [show 13 = 0 +
    13 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_13 :
    recurrence4Scalar2Exceptional.coeff 13 =
      -((173705075213 * 10 ^ 70 +
        1727399672261028515886243387642670124910954555922234924481790488269000) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 14,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (13 - x)) = _
  rw [show 14 = 0 +
    14 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_14 :
    recurrence4Scalar2Exceptional.coeff 14 =
      ((95664451921870 * 10 ^ 70 +
        6157203748954850320807206681551147803483152651954904588946370742116772) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 15,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (14 - x)) = _
  rw [show 15 = 0 +
    15 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_15 :
    recurrence4Scalar2Exceptional.coeff 15 =
      -((30441467267044865 * 10 ^ 70 +
        7051566293839850490886120935228483796639238482160555617121272909511570) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 16,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (15 - x)) = _
  rw [show 16 = 0 +
    16 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_16 :
    recurrence4Scalar2Exceptional.coeff 16 =
      ((6196711056169355055 * 10 ^ 70 +
        8683856431967323433880939541702877400852475945688910355901360071819092) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 17,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (16 - x)) = _
  rw [show 17 = 0 +
    17 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 17 = 17 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_17 :
    recurrence4Scalar2Exceptional.coeff 17 =
      -((822055291906476380919 * 10 ^ 70 +
        1030472421438163994975858983590375620099367028650832215454907627567472) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 18,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (17 - x)) = _
  rw [show 18 = 0 +
    18 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 18 = 18 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_18 :
    recurrence4Scalar2Exceptional.coeff 18 =
      ((118493394208465105481972 * 10 ^ 70 +
        1137807934493542690932244418472534522996630741424881041764632785582395) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 19,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (18 - x)) = _
  rw [show 19 = 0 +
    19 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_19 :
    recurrence4Scalar2Exceptional.coeff 19 =
      -((53996224809409609364745249 * 10 ^ 70 +
        3007173871495139656439598531176608374579216231423040980312024795613003) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 20,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (19 - x)) = _
  rw [show 20 = 0 +
    20 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 20 = 20 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_20 :
    recurrence4Scalar2Exceptional.coeff 20 =
      ((26691480465391869515593275305 * 10 ^ 70 +
        8332324123092334996652694109456423577778306907021119635730368442832848) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 21,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (20 - x)) = _
  rw [show 21 = 0 +
    21 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 21 = 21 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_21 :
    recurrence4Scalar2Exceptional.coeff 21 =
      -((9578349555902515077425828970480 * 10 ^ 70 +
        7176925708353396006213128446934388167531308757970604088810363257909730) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 22,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (21 - x)) = _
  rw [show 22 = 0 +
    22 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 22 = 22 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_22 :
    recurrence4Scalar2Exceptional.coeff 22 =
      ((2663206965145663388281203249429538 * 10 ^ 70 +
        8220960785558513985160489871218432685750035413232693540997631241524144) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 23,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (22 - x)) = _
  rw [show 23 = 0 +
    23 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 23 = 23 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_23 :
    recurrence4Scalar2Exceptional.coeff 23 =
      -((614531334346511716097699587603612310 * 10 ^ 70 +
        1347402135848934334367998234864196507015733420217034064795792338418548) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 24,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (23 - x)) = _
  rw [show 24 = 0 +
    24 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 24 = 24 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_24 :
    recurrence4Scalar2Exceptional.coeff 24 =
      ((125160289894485183431532074747912981038 * 10 ^ 70 +
        7313373726352536771191994520526597691463087331820794128891684410674039) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 25,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (24 - x)) = _
  rw [show 25 = 0 +
    25 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 25 = 25 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_25 :
    recurrence4Scalar2Exceptional.coeff 25 =
      -((24412740590490097928311686068537957506055 * 10 ^ 70 +
        1405493973871426178110385632793885784250047876120497039526665808874234) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 26,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (25 - x)) = _
  rw [show 26 = 0 +
    26 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 26 = 26 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_26 :
    recurrence4Scalar2Exceptional.coeff 26 =
      ((5064554825671483898870710403551853237535019 * 10 ^ 70 +
        1654638460993461577595593113104861425369321954023804633857665785181234) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 27,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (26 - x)) = _
  rw [show 27 = 0 +
    27 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 27 = 27 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_27 :
    recurrence4Scalar2Exceptional.coeff 27 =
      -((1185797780402166884801475711750932356493283096 * 10 ^ 70 +
        5194111328928071538787770879833039231970280079782699936189708743309953) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 28,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (27 - x)) = _
  rw [show 28 = 0 +
    28 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 28 = 28 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_28 :
    recurrence4Scalar2Exceptional.coeff 28 =
      ((299261012896607322934001413521392791540013209003 * 10 ^ 70 +
        1543555352319898020673552002438164672743838395503767379563591221936334) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 29,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (28 - x)) = _
  rw [show 29 = 0 +
    29 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 29 = 29 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_29 :
    recurrence4Scalar2Exceptional.coeff 29 =
      -((74763762971028525221395136561427976204193725270738 * 10 ^ 70 +
        3122691052710360077915261483032446431860022319395294986313608334703884) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 30,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (29 - x)) = _
  rw [show 30 = 0 +
    30 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 30 = 30 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_30 :
    recurrence4Scalar2Exceptional.coeff 30 =
      ((17521007756712227135096536598890886446706065044469441 * 10 ^ 70 +
        5649161582909810902893112247964239963430313443557353617905842343265469) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 31,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (30 - x)) = _
  rw [show 31 = 0 +
    31 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 31 = 31 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_31 :
    recurrence4Scalar2Exceptional.coeff 31 =
      -((3774020639627128489915451146738887252599469532833313688 * 10 ^ 70 +
        9915773581017070424290478490154336064900301553406600396922710201632707) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 32,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (31 - x)) = _
  rw [show 32 = 0 +
    32 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 32 = 32 +
      0 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num [Finset.sum_range_succ]

theorem recurrence4Scalar2Exceptional_coeff_32 :
    recurrence4Scalar2Exceptional.coeff 32 =
      ((744370190157732514490562186157869756726814763561421190649 * 10 ^ 70 +
        9207315210490483145058123638159320884596158046132222769282725898844148) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 33,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (32 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_33 :
    recurrence4Scalar2Exceptional.coeff 33 =
      -((134745142201276704343645665581086939426671011525611075355625 * 10 ^ 70 +
        0460875269293900024269606663258610572280725659244086874962285525314485) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 34,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (33 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_34 :
    recurrence4Scalar2Exceptional.coeff 34 =
      ((22474142397800155147545770066898222023580570613449760274155727 * 10 ^ 70 +
        0745315288995153906700628727228245867412191087668571020220325100258708) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 35,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (34 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_35 :
    recurrence4Scalar2Exceptional.coeff 35 =
      -((3467574336253949239294944866077072406199482694711092602314296521 * 10 ^ 70 +
        4927889861223156348115124738624110102031475699635142065097964591071442) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 36,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (35 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_36 :
    recurrence4Scalar2Exceptional.coeff 36 =
      ((496694224957885840824434703308680830943791961843224436778229472163 * 10 ^ 70 +
        6273392509277662521158946638563441359629808386118509443751533071167848) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 37,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (36 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_37 :
    recurrence4Scalar2Exceptional.coeff 37 =
      -((66254550542583417153438161474243164390677688153785926672216251399442 * 10 ^ 70 +
        8037924429465150979465723725877555686440720090956683098959720612384679) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 38,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (37 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_38 :
    recurrence4Scalar2Exceptional.coeff 38 =
      ((8252174577553750077192619512312844930119298422030845635621927776236870 * 10 ^ 70 +
        9583386946683107659910406257342766264201360932440178926586133985894885) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 39,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (38 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_39 :
    recurrence4Scalar2Exceptional.coeff 39 =
      -(((96 * 10 ^ 70 +
        1978482899363103600813279803805337099749328397283730707354136359488039) * 10 ^ 70 +
        7725417444251977920644213353063627121536410037502699071092249403793170) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 40,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (39 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_40 :
    recurrence4Scalar2Exceptional.coeff 40 =
      (((10517 * 10 ^ 70 +
        4647166881058206672036476019259820829312313379301806055983630695105738) * 10 ^ 70 +
        0336112719030672844136713810597094812440137247776489691755492952488760) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 41,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (40 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_41 :
    recurrence4Scalar2Exceptional.coeff 41 =
      -(((1080489 * 10 ^ 70 +
        1442970257540071470199490672883717328342782395713516900572460994337255) * 10 ^ 70 +
        9414920174872868139031651143484315661006155486352159860982722068071191) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 42,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (41 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_42 :
    recurrence4Scalar2Exceptional.coeff 42 =
      (((104480786 * 10 ^ 70 +
        6300449720959471192006610616146655120180748728705861261551189099999171) * 10 ^ 70 +
        0524060995944533526792795688815335899198943212740155654208099523006784) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 43,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (42 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_43 :
    recurrence4Scalar2Exceptional.coeff 43 =
      -(((9524524823 * 10 ^ 70 +
        1498605845919374259883679974454831923031689404288696115898042511400076) * 10 ^ 70 +
        6745300758675395890914631837577008813768772259212147193597599118122057) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 44,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (43 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_44 :
    recurrence4Scalar2Exceptional.coeff 44 =
      (((819739599674 * 10 ^ 70 +
        0252877269737248246085940337189579235473489478342365031518053694765730) * 10 ^ 70 +
        6619317538990720105032956859023143193555153185936979083456291598373062) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 45,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (44 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_45 :
    recurrence4Scalar2Exceptional.coeff 45 =
      -(((66700166526741 * 10 ^ 70 +
        7235417062906950234293833964786522087660738597788108446147723763106889) * 10 ^ 70 +
        8399234724475961360737498727030847156734454459349363581089114733209827) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 46,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (45 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_46 :
    recurrence4Scalar2Exceptional.coeff 46 =
      (((5137506263909010 * 10 ^ 70 +
        4712813322051027779056493623409306905688602463390259192036482928698493) * 10 ^ 70 +
        8340299711388991030816517485912091899141016689275805868821730738221738) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 47,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (46 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_47 :
    recurrence4Scalar2Exceptional.coeff 47 =
      -(((375038613032795644 * 10 ^ 70 +
        9144733394035066186655521086884530116557400463259313842480990182504030) * 10 ^ 70 +
        9189831682152945792785948825924771226700489786352186934199723967565356) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 48,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (47 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_48 :
    recurrence4Scalar2Exceptional.coeff 48 =
      (((25977222396226133037 * 10 ^ 70 +
        7146573311858467669997261970215438856314999599829621145036696375226385) * 10 ^ 70 +
        5425368412984743826632974086641629937533376770070412263666671318382411) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 49,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (48 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_49 :
    recurrence4Scalar2Exceptional.coeff 49 =
      -(((1709116197558616271276 * 10 ^ 70 +
        0917835438451524247422444782151736403802546028242587462257193760420749) * 10 ^ 70 +
        9429607008765577334800698780337334263238506621116704094473081724941995) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 50,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (49 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_50 :
    recurrence4Scalar2Exceptional.coeff 50 =
      (((106919813410542031557483 * 10 ^ 70 +
        4521793956328756932999789454029706931969555659759811817798896420618621) * 10 ^ 70 +
        8539103397089728741491236027170999906338775052955758247669905934279368) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 51,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (50 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_51 :
    recurrence4Scalar2Exceptional.coeff 51 =
      -(((6366147501062080439201823 * 10 ^ 70 +
        5497756446958090461589782982674399026216628507501522032190361774824740) * 10 ^ 70 +
        1165858199202209004349816887547071225456330262027562042567448882640226) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 52,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (51 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_52 :
    recurrence4Scalar2Exceptional.coeff 52 =
      (((361103469695355636232795673 * 10 ^ 70 +
        0611613374005917502564055010917673963648779061044696267111243186049749) * 10 ^ 70 +
        0577081430776937432156803262231708424191966562532945765554212643221087) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 53,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (52 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_53 :
    recurrence4Scalar2Exceptional.coeff 53 =
      -(((19530329191360495105512826959 * 10 ^ 70 +
        7660293834124123238792175662523917001078982263414075102320481993172104) * 10 ^ 70 +
        7476510684235756252082924551205818728957931978522948720458150671771656) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 54,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (53 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_54 :
    recurrence4Scalar2Exceptional.coeff 54 =
      (((1008045528215614057506411249812 * 10 ^ 70 +
        7287048385521200760183681007776141164799051195319496799401335116749075) * 10 ^ 70 +
        6533250061045345052261857695505760482934277786383760204240770905980085) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 55,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (54 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_55 :
    recurrence4Scalar2Exceptional.coeff 55 =
      -(((49693273564588848642215368285532 * 10 ^ 70 +
        5231236675683210860651423640280245962561732209104755225473394008476290) * 10 ^ 70 +
        8033169859403511034266439375305483797700865835227077322297951108502895) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 56,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (55 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_56 :
    recurrence4Scalar2Exceptional.coeff 56 =
      (((2341540276579890987426789707028688 * 10 ^ 70 +
        5814806846408942158125036209416212015387530035563514204894573223097346) * 10 ^ 70 +
        4208768291461252972455953977583145797433764567423124292041877564269105) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 57,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (56 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_57 :
    recurrence4Scalar2Exceptional.coeff 57 =
      -(((105540303377277220760307383520851520 * 10 ^ 70 +
        9976800180525969577778346407161914918455249363220307599462225842327687) * 10 ^ 70 +
        7786586273670376445960239058554971776794337565296414433973022497546447) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 58,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (57 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_58 :
    recurrence4Scalar2Exceptional.coeff 58 =
      (((4553665141512237208278187167717321286 * 10 ^ 70 +
        4849123567852286457415754629228271143105554475755804534148611750375165) * 10 ^ 70 +
        7320003595770788280571748720907700368864080343172310895245447350849765) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 59,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (58 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_59 :
    recurrence4Scalar2Exceptional.coeff 59 =
      -(((188205040378907022332069624482048891067 * 10 ^ 70 +
        5094907831142730222761191726993855213300421153234848155492263484929512) * 10 ^ 70 +
        4134682680097914996906258419844660050330752656035885402341726519364054) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 60,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (59 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_60 :
    recurrence4Scalar2Exceptional.coeff 60 =
      (((7456222001118343109907928523225104171510 * 10 ^ 70 +
        2175084227371410646741632998706883380660598812436136391398904579355970) * 10 ^ 70 +
        0021808693189594156159090279402390565916973892306869177710971422105365) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 61,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (60 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_61 :
    recurrence4Scalar2Exceptional.coeff 61 =
      -(((283336873766229535400209230472162428157557 * 10 ^ 70 +
        0856265118267517105887737880853449088507289922423444956680776103048959) * 10 ^ 70 +
        6826266967865347405697850416435964188343931050214278625136613055618048) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 62,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (61 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_62 :
    recurrence4Scalar2Exceptional.coeff 62 =
      (((10333634770554616270789478779374367399320353 * 10 ^ 70 +
        2812953472348329560492947528210351833261187873179450215150491393691403) * 10 ^ 70 +
        8570020468481389189250609051894781773376747688532755018380560241752620) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 63,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (62 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_63 :
    recurrence4Scalar2Exceptional.coeff 63 =
      -(((361933003610415237462948690226963945219586550 * 10 ^ 70 +
        9829819636644436944092016378820027505335068612290397705734154540141582) * 10 ^ 70 +
        1881523150118890238106521344622611701895772905551728463379605734187654) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 64,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (63 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_64 :
    recurrence4Scalar2Exceptional.coeff 64 =
      (((12180871667915027792003282731681802327406837753 * 10 ^ 70 +
        9811340329576463746638523547254939348075642566376107363479195768338929) * 10 ^ 70 +
        9689330319658903795340439765763614228357804883576080441371898637356295) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 65,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (64 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_65 :
    recurrence4Scalar2Exceptional.coeff 65 =
      -(((394134798312444121153954569766312517504227093894 * 10 ^ 70 +
        4612664498901330693423805943677042424982806479157165883601129383187192) * 10 ^ 70 +
        1224504133082364291894264436380453663955580633629371216461957625151312) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 66,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (65 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_66 :
    recurrence4Scalar2Exceptional.coeff 66 =
      (((12267611258347457332072574920735949016897397628580 * 10 ^ 70 +
        3026462221900349493124691038138051827816799675530396861860538670372519) * 10 ^ 70 +
        0135653342280552867259059249405826679351735585848465083306607943794306) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 67,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (66 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_67 :
    recurrence4Scalar2Exceptional.coeff 67 =
      -(((367492420185697890024710384189074991815423674167186 * 10 ^ 70 +
        9727383917673011043134397689950128642292202326526244917013083658770822) * 10 ^ 70 +
        5479006995418829450541327399780110513513919096624211119065439724785768) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 68,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (67 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_68 :
    recurrence4Scalar2Exceptional.coeff 68 =
      (((10600499010260126018214505421325971098872958521980934 * 10 ^ 70 +
        9074864345063009733117499221754523504403461264947458428259241003474199) * 10 ^ 70 +
        5072762454344277383880826349184993014886435247083455184248856187925466) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 69,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (68 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_69 :
    recurrence4Scalar2Exceptional.coeff 69 =
      -(((294579456981739201001070643712309214289461811977243476 * 10 ^ 70 +
        8147696521877086733744889015055187017870836889246555160587455857724625) * 10 ^ 70 +
        5708975708333317373005332473400519692081851048140568272655487581454187) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 70,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (69 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_70 :
    recurrence4Scalar2Exceptional.coeff 70 =
      (((7890018421485030188283975746388493176929228969028914293 * 10 ^ 70 +
        7401337651874934654973417820286045685281701210617956569093464012663523) * 10 ^ 70 +
        4762862164780508923933021671904553131435897855616651981603128628319454) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 71,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (70 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_71 :
    recurrence4Scalar2Exceptional.coeff 71 =
      -(((203773110473985435552096591706626486543591065455686704753 * 10 ^ 70 +
        8377232661590928570993671313024468150477606466773462892131320771948954) * 10 ^ 70 +
        7944148565271497927690539235572494125472787480611530521865102925870348) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 72,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (71 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_72 :
    recurrence4Scalar2Exceptional.coeff 72 =
      (((5076866800878318995401059055286427006339835271269577910248 * 10 ^ 70 +
        4337463321642997070452469985585326657148474721388519705426622070814950) * 10 ^ 70 +
        8469510042802031144686115618062109311317015873127930808955657572825349) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 73,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (72 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_73 :
    recurrence4Scalar2Exceptional.coeff 73 =
      -(((122068729070473066561385079518537108842699207943764351599047 * 10 ^ 70 +
        6283909202042483147478556627239097751241741488197333786085105810022028) * 10 ^ 70 +
        8763900341787630068628936415561575930986800080606691501117197288755489) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 74,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (73 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_74 :
    recurrence4Scalar2Exceptional.coeff 74 =
      (((2833646307629052120020208476808548028271929419141271751722291 * 10 ^ 70 +
        4173437336226886370947502487216352240605122340309449562378679963139196) * 10 ^ 70 +
        9560517506917619959142556870559071930352173792819368053532649693695723) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 75,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (74 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_75 :
    recurrence4Scalar2Exceptional.coeff 75 =
      -(((63530954793408727949463510310107578055101367455847220223779827 * 10 ^ 70 +
        3249617909780148272475544014364514167744087853594726047953871468715947) * 10 ^ 70 +
        3397799040052990331873969390042240504674440988490535716472188609636151) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 76,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (75 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_76 :
    recurrence4Scalar2Exceptional.coeff 76 =
      (((1376203939417393074287142165966501704117884789863580759219115292 * 10 ^ 70 +
        7771068463660168086424097886119928064546838427542725249641487840087203) * 10 ^ 70 +
        8929864465819673214282032331936077402937564626612369307419565109654198) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 77,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (76 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_77 :
    recurrence4Scalar2Exceptional.coeff 77 =
      -(((28813116373156583416493138191717783908624003021160737857403243069 * 10 ^ 70 +
        6937576861504151183502969110626824811044076916798336035701817383017596) * 10 ^ 70 +
        7213268301898584380976665257554773521826425643031319873523654003873703) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 78,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (77 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_78 :
    recurrence4Scalar2Exceptional.coeff 78 =
      (((583247936918523322405219394560018080326548219370500748758433858616 * 10 ^ 70 +
        4396601443505606314386628560021370025585682793151802262570560295943438) * 10 ^ 70 +
        7917870832810334128751407932238427187283746017296186802274798363925958) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 79,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (78 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_79 :
    recurrence4Scalar2Exceptional.coeff 79 =
      -(((11418534106362314021031893534625480344076358470697960360475099435029 * 10 ^ 70 +
        4476845531209768823261306347871241105880889375177441391191988127921200) * 10 ^ 70 +
        6014143506002180865396949942435657135503760286174331203516300860502680) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 80,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (79 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_80 :
    recurrence4Scalar2Exceptional.coeff 80 =
      (((216268505010626633970719224233815090356512113931680465861222843683191 * 10 ^ 70 +
        0224819988342065598782324877572083863553428980170090712201798485672721) * 10 ^ 70 +
        8308901648257281038783610973339556402858964310421956349483202117133622) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 81,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (80 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_81 :
    recurrence4Scalar2Exceptional.coeff 81 =
      -(((3963934266467169879746101252201840681884375368608569740758550059864474 * 10 ^ 70 +
        3262457108262430640311862068843004905563055210356228909562280467944676) * 10 ^ 70 +
        6708662679880046358692001796129222031269089689232584364300823127543783) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 82,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (81 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_82 :
    recurrence4Scalar2Exceptional.coeff 82 =
      ((((7 * 10 ^ 70 +
        0327785428952891855346751639387451726196540564802168850757892444283787) * 10 ^ 70 +
        2766131218216069959183955889413856205485816623686406882747503187127934) * 10 ^ 70 +
        1864986232365741314660286511886685447879714415087912577077745501987534) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 83,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (82 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_83 :
    recurrence4Scalar2Exceptional.coeff 83 =
      -((((120 * 10 ^ 70 +
        8103733132169175833085295531833212059262692465568092708917960764023418) * 10 ^ 70 +
        5429104983879760540237532287155074661924169385818985417624827186054559) * 10 ^ 70 +
        8018647939963601800914986238941432348026848292216654542296348223826375) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 84,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (83 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_84 :
    recurrence4Scalar2Exceptional.coeff 84 =
      ((((2009 * 10 ^ 70 +
        8320845051244183036736924358603458295281979231333192362669929343646808) * 10 ^ 70 +
        2324188626668863826708531246234700066676489589500619627390792216927241) * 10 ^ 70 +
        8556977618594167086730084023088983711135334644599045027751214416401377) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 85,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (84 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_85 :
    recurrence4Scalar2Exceptional.coeff 85 =
      -((((32388 * 10 ^ 70 +
        1891598252836057366001273180373154930736861041065382453803343498002800) * 10 ^ 70 +
        4947153542201174939672019177875996982768790070195144865290713633675813) * 10 ^ 70 +
        2249674222562482436701875537570324374774781702491858713823865304110780) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 86,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (85 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_86 :
    recurrence4Scalar2Exceptional.coeff 86 =
      ((((505672 * 10 ^ 70 +
        1816794822746854557301069834170694087137280529263377164442130555984724) * 10 ^ 70 +
        2976252151401258083096506873990839339239469902442148395971675372429142) * 10 ^ 70 +
        1176752207711999726765909423124347164856066889665009623751259723701539) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 87,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (86 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_87 :
    recurrence4Scalar2Exceptional.coeff 87 =
      -((((7650354 * 10 ^ 70 +
        5651366028986955419930548740395956356317395178002194321148407141553101) * 10 ^ 70 +
        8908327073906834153955475388970672458354778706108596343885141784828548) * 10 ^ 70 +
        0495996828716032202781961304675321109356783920301825986325376005875130) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 88,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (87 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_88 :
    recurrence4Scalar2Exceptional.coeff 88 =
      ((((112173025 * 10 ^ 70 +
        1014271826705591564600490371419934191353094806272398946041862251748331) * 10 ^ 70 +
        9385243504257050161297690224187204434751882425512948787949459798062844) * 10 ^ 70 +
        8252412366116402327034980162369544360847997631642782338272203921961986) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 89,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (88 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_89 :
    recurrence4Scalar2Exceptional.coeff 89 =
      -((((1594199376 * 10 ^ 70 +
        9951422802244038694955779068396319447076475777773354558457240445662992) * 10 ^ 70 +
        3543465925251776842556792586386994101496724213441061045342520964775331) * 10 ^ 70 +
        5418938611477406452273678718227363471091038872057082696681176820834527) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 90,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (89 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_90 :
    recurrence4Scalar2Exceptional.coeff 90 =
      ((((21962646434 * 10 ^ 70 +
        3868613990761005396241886321541781911013479156942041832535218892847412) * 10 ^ 70 +
        6173887448320394141051721365453259981482184090558148842537798142592438) * 10 ^ 70 +
        2549396664836192893628299785390086169113651566015470214052223183232705) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 91,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (90 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_91 :
    recurrence4Scalar2Exceptional.coeff 91 =
      -((((293319626197 * 10 ^ 70 +
        3447410119837365893968994414492271447377595899826330533152269505083968) * 10 ^ 70 +
        6026522539486362807465515113175918935052036722949107571084703963488299) * 10 ^ 70 +
        4696631253089978286460304611832123354400942937362561210322267929030486) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 92,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (91 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_92 :
    recurrence4Scalar2Exceptional.coeff 92 =
      ((((3797719460119 * 10 ^ 70 +
        2692322279571144288920656127835093311784358866087481443440855440136395) * 10 ^ 70 +
        3203337658173371661606310316691695560199772328741600912220357409043286) * 10 ^ 70 +
        3697266195434010218246062666100425557558924703931942918697265513184743) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 93,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (92 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_93 :
    recurrence4Scalar2Exceptional.coeff 93 =
      -((((47667558040614 * 10 ^ 70 +
        5269739823174787906018624637246875053092313265731158866960484212320890) * 10 ^ 70 +
        5883196769385640787394324992857893997717089940495989674725931985352636) * 10 ^ 70 +
        2737387500863919792471688791211498074463620372739248784316497465099385) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 94,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (93 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_94 :
    recurrence4Scalar2Exceptional.coeff 94 =
      ((((579980561785031 * 10 ^ 70 +
        5379536901384826645993911039534110726492029773325872610705634284895467) * 10 ^ 70 +
        7611319689137520012004847708266726170458433398243402645647120331605135) * 10 ^ 70 +
        9443456638084170967120349748009270754844343988271761505468060478980333) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 95,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (94 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_95 :
    recurrence4Scalar2Exceptional.coeff 95 =
      -((((6839785184383801 * 10 ^ 70 +
        1267327719604200005572517365606054232733500611656441134392036287980258) * 10 ^ 70 +
        2405541567779800143340361892373639405883334046361127322328447756924555) * 10 ^ 70 +
        0351631383271611129164138191996920460574680672234583836029494136008774) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 96,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (95 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_96 :
    recurrence4Scalar2Exceptional.coeff 96 =
      ((((78168026090050736 * 10 ^ 70 +
        9108937681427238741987100890495330271127816972086238357274022430624443) * 10 ^ 70 +
        4941359420470885606859484102525924176753124036215288614571845167271821) * 10 ^ 70 +
        3467504129443510801111556345656520301306329433295947255605553213733576) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 97,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (96 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_97 :
    recurrence4Scalar2Exceptional.coeff 97 =
      -((((865481804301612525 * 10 ^ 70 +
        3998707162267701686278563061114347589715103975793259629647627530641531) * 10 ^ 70 +
        0608076644962540046135822779135810696782436954277735147863711934677576) * 10 ^ 70 +
        7097573849321945429512431029609716206546622031850361964102782867175983) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 98,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (97 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_98 :
    recurrence4Scalar2Exceptional.coeff 98 =
      ((((9280487788395303546 * 10 ^ 70 +
        4112494451476458428281005065232234185074946195062931775085531092393037) * 10 ^ 70 +
        0873758779608173199806983350486416800779010278315756211763820967634909) * 10 ^ 70 +
        2072476612721963396912015856122600503228479434075043870420831767989634) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 99,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (98 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_99 :
    recurrence4Scalar2Exceptional.coeff 99 =
      -((((96328930018378350920 * 10 ^ 70 +
        3977785363897100925400270215965754717091212033095810127032226276561018) * 10 ^ 70 +
        1103131833700465467913902443102211574542914788893771007636109417606238) * 10 ^ 70 +
        7490134667313602152416386335329984020518114022086366985826672624649828) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 100,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (99 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_100 :
    recurrence4Scalar2Exceptional.coeff 100 =
      ((((967247279439873639770 * 10 ^ 70 +
        6444856737583273751985806076881622533541493623931866287796263555693998) * 10 ^ 70 +
        1617862031121039181750207389475632952830109401107388724858356047631495) * 10 ^ 70 +
        7727238591985879843532276668228861249191325606178672824108001124413901) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 101,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (100 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_101 :
    recurrence4Scalar2Exceptional.coeff 101 =
      -((((9387451702670520996263 * 10 ^ 70 +
        4634322865118638613713640391779643778662256944570183247342619936696988) * 10 ^ 70 +
        2931730200427358235479046482570176152625299378471257733586988869202421) * 10 ^ 70 +
        8715213781057831619840140710364085716476735809855924825360111326993839) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 102,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (101 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_102 :
    recurrence4Scalar2Exceptional.coeff 102 =
      ((((87964211463094036790843 * 10 ^ 70 +
        7774777170788156354468487182039713501330677863452548354167030570322233) * 10 ^ 70 +
        1223280370781161452830778429124285163393442191429484572372666904639014) * 10 ^ 70 +
        2850188968515436183296983637558445598187018757117844256379798304814163) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 103,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (102 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_103 :
    recurrence4Scalar2Exceptional.coeff 103 =
      -((((794644246613107900008031 * 10 ^ 70 +
        2732056256938579558781153986361625032522667672847947065599681436664447) * 10 ^ 70 +
        8724736061320936736085621368887096909268790947920583619358439867113166) * 10 ^ 70 +
        9223009852583025676671189965171614871137231259655437216713758501651295) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 104,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (103 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_104 :
    recurrence4Scalar2Exceptional.coeff 104 =
      ((((6906924551169108083544241 * 10 ^ 70 +
        9276807559969918137514556806606871846442596274379363654029420096578701) * 10 ^ 70 +
        9353018925717692002379695105235711701577574685472310791665280590162057) * 10 ^ 70 +
        7648451812202463973433982716774775561706466835073597367493169265803144) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 105,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (104 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_105 :
    recurrence4Scalar2Exceptional.coeff 105 =
      -((((57603744876756213002464379 * 10 ^ 70 +
        2208170751400262275795919555913399516663863796627810391648825974784752) * 10 ^ 70 +
        5480738535871932677837418731904872048599346676991128375710633501131156) * 10 ^ 70 +
        0927596128957765746267509301918097059061590190812567920892567713275112) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 106,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (105 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_106 :
    recurrence4Scalar2Exceptional.coeff 106 =
      ((((459171460516979044308936501 * 10 ^ 70 +
        2233263300541774475167149540474725390495959969338236646163010719374590) * 10 ^ 70 +
        9591595201495866712036720603804884721005023624304369774741504378344813) * 10 ^ 70 +
        8449957428580462694042521554308513052959450110940820055762483470984667) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 107,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (106 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_107 :
    recurrence4Scalar2Exceptional.coeff 107 =
      -((((3478062443330108187897568985 * 10 ^ 70 +
        5269475574303639596637158861097049373402009812416512632706780634538312) * 10 ^ 70 +
        7783849158332726175383517563146169044264605351487890051541624890597210) * 10 ^ 70 +
        2113903514293166613592575074291284302590046371768447264659197214972557) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 108,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (107 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_108 :
    recurrence4Scalar2Exceptional.coeff 108 =
      ((((24806492284219419067255345435 * 10 ^ 70 +
        1812216829178407000145926987700061505504372118672522777490510890162968) * 10 ^ 70 +
        6392760717705231218426220855887081919814770668885107246256840395962823) * 10 ^ 70 +
        4172001677838124326518749607546846481613463358595069065833442055825825) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 109,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (108 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_109 :
    recurrence4Scalar2Exceptional.coeff 109 =
      -((((163998869471952652057543164691 * 10 ^ 70 +
        4230916326185188356819548807164837109923838598931579596061473015862723) * 10 ^ 70 +
        4286731378928722993401605430998068842710686249987019825613838720348008) * 10 ^ 70 +
        0224315712187000564725656803010933733988918164304199850604764118378359) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 110,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (109 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_110 :
    recurrence4Scalar2Exceptional.coeff 110 =
      ((((974665671384033167128160638342 * 10 ^ 70 +
        5788112918207898205852896452036831550095700423994564676933218670979572) * 10 ^ 70 +
        4826613372943435442631256775165340393054130260226416439377880242029912) * 10 ^ 70 +
        0829825356032148312214981191306636684282001267903550299931683650366967) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 111,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (110 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_111 :
    recurrence4Scalar2Exceptional.coeff 111 =
      -((((4833863892907388210402209638387 * 10 ^ 70 +
        5508526278120303096883405573323073052605653917836502130116206011425492) * 10 ^ 70 +
        8298009272048136692080020293207682826879781646694810962103232281222541) * 10 ^ 70 +
        2253766035018378263545792478852226480297055680140558109594141136654554) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 112,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (111 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_112 :
    recurrence4Scalar2Exceptional.coeff 112 =
      ((((14938610713561557066049436628712 * 10 ^ 70 +
        1407414889211618372699101928823815440007560389958524439863178820064150) * 10 ^ 70 +
        6312443880018368438226895879385633674619497074883649959889949522110972) * 10 ^ 70 +
        8206763833251726390337453290170158532852661560329670633366583727621807) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 113,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (112 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_113 :
    recurrence4Scalar2Exceptional.coeff 113 =
      ((((53978724493099406360328516529408 * 10 ^ 70 +
        3453792047792033903319446799123294062692296108663234577797241838387698) * 10 ^ 70 +
        0966658759543469154125264414302317158079294451734754430238857018510965) * 10 ^ 70 +
        9744444600673965207835175176224256292418841104013896412848988077438860) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 114,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (113 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_114 :
    recurrence4Scalar2Exceptional.coeff 114 =
      -((((1576049987613263921384871057778352 * 10 ^ 70 +
        4102649446629459919060870353054379905273683050492048075159806173757411) * 10 ^ 70 +
        7402840722674466561465208080674026360030306225341241822839553146302335) * 10 ^ 70 +
        0065809249453229775218022301101196375047736212710638494403897871734586) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 115,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (114 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_115 :
    recurrence4Scalar2Exceptional.coeff 115 =
      ((((19188544922773918352187293585537902 * 10 ^ 70 +
        3150912026536230648320904161335901816876241365982051260697099137696267) * 10 ^ 70 +
        6973467704208237784288411676218347900376778235663935634581290537004785) * 10 ^ 70 +
        1349749411139884651041304938542664309910663522536707311095972986184047) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 116,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (115 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_116 :
    recurrence4Scalar2Exceptional.coeff 116 =
      -((((183346514575472565182275113544458480 * 10 ^ 70 +
        1313554325606584246480454390480103723637336157165304283908315218518699) * 10 ^ 70 +
        5043419205974208003488984387731376511564125633982087936142157615402415) * 10 ^ 70 +
        2616811818090019150794911038212011084589454742329036791166015000232052) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 117,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (116 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_117 :
    recurrence4Scalar2Exceptional.coeff 117 =
      ((((1528224159845085773549791211644897586 * 10 ^ 70 +
        2685863783218331483056400702191588003904448371471993583830452565671432) * 10 ^ 70 +
        8560701160217782783894922805473369695301496309976603577221150226490843) * 10 ^ 70 +
        1445156487764116454335245166494863465838418352423354997795967106225442) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 118,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (117 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_118 :
    recurrence4Scalar2Exceptional.coeff 118 =
      -((((11499449592048197101391599294885052096 * 10 ^ 70 +
        9438330741569356807283182308561035972924184313069392689481815648630799) * 10 ^ 70 +
        9533660525869676701469054365891325505048077103408022293096705044147692) * 10 ^ 70 +
        9478438355716949639587181878562646322993724645192886123187387002421725) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 119,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (118 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_119 :
    recurrence4Scalar2Exceptional.coeff 119 =
      ((((78935050597835869839248332923844299387 * 10 ^ 70 +
        4861786192789788687071708173718220487526251454485392508441323139774857) * 10 ^ 70 +
        1960351363899636484364636036950740293701818535566063004091663122148749) * 10 ^ 70 +
        0424008138163570590483744907453121622912949995033436201978458948465917) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 120,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (119 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_120 :
    recurrence4Scalar2Exceptional.coeff 120 =
      -((((492326720372576766866288832766522904772 * 10 ^ 70 +
        8673227785414358764616798481723847718047429872042551513853417895964093) * 10 ^ 70 +
        9999286409225197395564403538800770511944134214198993091033470704898088) * 10 ^ 70 +
        5898210848998511334741773920677133588651612653857501980671847978296215) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 121,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (120 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_121 :
    recurrence4Scalar2Exceptional.coeff 121 =
      ((((2731583380078680837741404553192637006468 * 10 ^ 70 +
        6126628465647184332414916228072625962757480131284761003064183722134576) * 10 ^ 70 +
        7624538475514224720865271630785100129205237351966757760099532723139662) * 10 ^ 70 +
        8366435911933270529495595902051715896248265694994265958334482299413540) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 122,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (121 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_122 :
    recurrence4Scalar2Exceptional.coeff 122 =
      -((((12691889947756002256856949135989912356986 * 10 ^ 70 +
        8434954438109070618768005746875522776400330683176994208651296628443305) * 10 ^ 70 +
        3103139590171136367855982546499460625310526259139625867025809340080908) * 10 ^ 70 +
        8960471031560830858655916366943663852376364536769282483052509095254588) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 123,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (122 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_123 :
    recurrence4Scalar2Exceptional.coeff 123 =
      ((((39381254357532165299450989517402909968297 * 10 ^ 70 +
        6043061155333342482129802432823396197130638272192940274121229478179737) * 10 ^ 70 +
        5822281983760262820492199774324136183077923680099297697788335224935466) * 10 ^ 70 +
        0477791865737463033525819420024936976837020126381729106164073402060361) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 124,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (123 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_124 :
    recurrence4Scalar2Exceptional.coeff 124 =
      ((((61177122351785499414718863808914915128511 * 10 ^ 70 +
        7979081608015293442249569388111472212135034206974084284474101153637540) * 10 ^ 70 +
        6584547490548172305101144660459037770751567951664967017729763635260026) * 10 ^ 70 +
        5677061722604659381948821593527775300371095311144280833518476527442479) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 125,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (124 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_125 :
    recurrence4Scalar2Exceptional.coeff 125 =
      -((((2465991108514156010234356248698495463471980 * 10 ^ 70 +
        9284797976577762791667765529266205763642299805515515195004107457997015) * 10 ^ 70 +
        3448600252633666450820064574840362010849510407787463699831187591113474) * 10 ^ 70 +
        2835802311856057980314138662491501489027825057547696259636801978432592) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 126,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (125 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_126 :
    recurrence4Scalar2Exceptional.coeff 126 =
      ((((27958618972115298414492877990373609753722378 * 10 ^ 70 +
        4306396753039046914376403352591610822077617557939478519474163170062813) * 10 ^ 70 +
        5253839195785367027800861755220743693399212083660967531719800625045177) * 10 ^ 70 +
        6904621679136151101041724122311076977097054807336490809242999310098367) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 127,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (126 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_127 :
    recurrence4Scalar2Exceptional.coeff 127 =
      -((((240569764488697440646937076159524413820224093 * 10 ^ 70 +
        5977289262936371898124223040278454046187479279578589553871374205999829) * 10 ^ 70 +
        3160720048185136928359606290666916716364181234544762284603936177244287) * 10 ^ 70 +
        3442775704069636744582935076127858964354123740134500499619239607375000) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 128,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (127 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_128 :
    recurrence4Scalar2Exceptional.coeff 128 =
      ((((1784018229405321890999275335649641400740331909 * 10 ^ 70 +
        9564965374785000774591836084994684298418702398620494226774504910492522) * 10 ^ 70 +
        0829303639607144323290668163500947583493512468013171273549386958955239) * 10 ^ 70 +
        6782995826674377637175308385915148697765193715892194043209300173465349) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 129,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (128 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_129 :
    recurrence4Scalar2Exceptional.coeff 129 =
      -((((11858419375935660260466005247572765578619754284 * 10 ^ 70 +
        7570488071007672793661880095431851159896998057690422569275354968000486) * 10 ^ 70 +
        5846449985636091468041731591799444825975333986096210458340991773122967) * 10 ^ 70 +
        0461200191868749656200946613979749332141813184265911646732359147784613) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 130,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (129 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_130 :
    recurrence4Scalar2Exceptional.coeff 130 =
      ((((71459860490427004708781222113706132041186598740 * 10 ^ 70 +
        7728363664444889054295785150754517045203380582608699036027178795927823) * 10 ^ 70 +
        1583500843905333868556141904116003077970352531266920463124611509043690) * 10 ^ 70 +
        9926760801987831449105208336512584510265954425403670492834159544937230) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 131,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (130 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_131 :
    recurrence4Scalar2Exceptional.coeff 131 =
      -((((388184744812426264652274790377321122389353776858 * 10 ^ 70 +
        3344985593805900322772130742922788088914100036839350243361165992425516) * 10 ^ 70 +
        5146562744711012952351520237394433793851702961133996516979033991214590) * 10 ^ 70 +
        9987887533213461202295962846462853807964480407637248015183719028110855) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 132,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (131 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_132 :
    recurrence4Scalar2Exceptional.coeff 132 =
      ((((1848237967274368580339500460262037807931803099192 * 10 ^ 70 +
        0676980503353624138730980684414367747161258499077936971145231708908229) * 10 ^ 70 +
        0904767632956453302023701377284552560503767265470094248647031352151658) * 10 ^ 70 +
        2291780851582821416054703516238786917704232208260603424773945399852339) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 133,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (132 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_133 :
    recurrence4Scalar2Exceptional.coeff 133 =
      -((((7073272815945886766639795655883757950245820555843 * 10 ^ 70 +
        5459890787058805202460207218363153618366458395038493162272544822885737) * 10 ^ 70 +
        0735980424749569592667454216116821447982083961094125016937803597123198) * 10 ^ 70 +
        7804463955956006290194909300568255454867315868050712459371367852767055) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 134,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (133 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_134 :
    recurrence4Scalar2Exceptional.coeff 134 =
      ((((14207070660475576161470744456201050576710933526728 * 10 ^ 70 +
        9196450068745333582497051630961883902949882639679701158112796317667748) * 10 ^ 70 +
        5400294914465932910712169719135703985811076521809991019342942895972945) * 10 ^ 70 +
        7127728594735603131672608965134917439746636416868211817801420670440152) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 135,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (134 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_135 :
    recurrence4Scalar2Exceptional.coeff 135 =
      ((((90132913206884898016700751781190773892207495617760 * 10 ^ 70 +
        0618820978673256019212804252723187860149615100788267939725588029682514) * 10 ^ 70 +
        8820182978376511778587306172847190618824476499825547618888689887323530) * 10 ^ 70 +
        4517683549577114740478731469486762191731857572483077867869933395869760) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 136,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (135 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_136 :
    recurrence4Scalar2Exceptional.coeff 136 =
      -((((1515133553290292639151509361150693070896144689089754 * 10 ^ 70 +
        9669227813633769273872227328681162803570415941637713841102445884425256) * 10 ^ 70 +
        2911139551537359030614217898638772393673785427627796875447745579693441) * 10 ^ 70 +
        7925823971356441621895331528471849680357759791822554107107820046945954) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 137,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (136 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_137 :
    recurrence4Scalar2Exceptional.coeff 137 =
      ((((13878708166953875157380384211850821962910579058522091 * 10 ^ 70 +
        4699372806364147060074932195945671833696761027427091177174639889118336) * 10 ^ 70 +
        2556775881410955672583167760018421236071869085168011695133218807900109) * 10 ^ 70 +
        8037763418531787167581286054464538976948761392256137930856093371456491) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 138,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (137 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_138 :
    recurrence4Scalar2Exceptional.coeff 138 =
      -((((103117443693573760948817730057310879177040281773787906 * 10 ^ 70 +
        2000147070788391971993721707056305224783007892055073254508752426272678) * 10 ^ 70 +
        9705639939536092253852856429281118593860133353958149207099784151026090) * 10 ^ 70 +
        7809482630659511837194542297280245120374928541752564689691232094414020) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 139,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (138 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_139 :
    recurrence4Scalar2Exceptional.coeff 139 =
      ((((676921950681576377946335627898939438464644361227482784 * 10 ^ 70 +
        0591368351717812121294564790466300656490283902530654426965358794844841) * 10 ^ 70 +
        6817174729355661830699196615773951610335605549317686513456686218853310) * 10 ^ 70 +
        1173244006280704644387838396785461220761594384992638101052048780931123) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 140,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (139 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_140 :
    recurrence4Scalar2Exceptional.coeff 140 =
      -((((4047748545511214493025726596598404970078464922554957176 * 10 ^ 70 +
        5852249888170662913093076348321074673656745375303084009399326440258317) * 10 ^ 70 +
        7463708151835366376530725077980104206397300382537605600086549148822904) * 10 ^ 70 +
        7814247454841469657005501878801194212732892320451296354636383309789678) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 141,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (140 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_141 :
    recurrence4Scalar2Exceptional.coeff 141 =
      ((((22287305727084643390943555395391811940911674152195681129 * 10 ^ 70 +
        0781980150721911663569357009651722393276643905477900858916607220574622) * 10 ^ 70 +
        4055873336409290186500385624667285256713275349990767923033642178443528) * 10 ^ 70 +
        4887239031997675764172895234174007481939051185196883577164662442173883) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 142,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (141 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_142 :
    recurrence4Scalar2Exceptional.coeff 142 =
      -((((112897789936671604837641738048293418899551170469689035634 * 10 ^ 70 +
        4660685991416420534288295835389029107927230580805095044106301913601332) * 10 ^ 70 +
        5407974448661923291795884737473452838620596135932167737905565070221805) * 10 ^ 70 +
        0184764042811195780202321441649603152188334219380286295657293111292865) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 143,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (142 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_143 :
    recurrence4Scalar2Exceptional.coeff 143 =
      ((((518996633386194798597242997247492891839083680072907702402 * 10 ^ 70 +
        5924182927033162434030987199743468078751461904744541759074830291850062) * 10 ^ 70 +
        6466695267389412882905802322597811676407060178567810948636538553014198) * 10 ^ 70 +
        5713015910029872715851485059858539531923770706270814211380391334654823) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 144,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (143 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_144 :
    recurrence4Scalar2Exceptional.coeff 144 =
      -((((2083259298505801494878142426032788712483730934386380958413 * 10 ^ 70 +
        1890329827059605974861805890972997987131536709205958410460877750395480) * 10 ^ 70 +
        4925365359814849123900737863407651385387640072720288494283657492049555) * 10 ^ 70 +
        7610029892141844063390406074801573719082955763078045243113825570416360) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 145,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (144 - x)) = _
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

theorem recurrence4Scalar2Exceptional_coeff_145 :
    recurrence4Scalar2Exceptional.coeff 145 =
      ((((6478358606083984888257366023134838887075803881248684105890 * 10 ^ 70 +
        7142274347859859569846184455065778691927950985202192776385060499479757) * 10 ^ 70 +
        5347318155857898749160434086952946909978269184871851027211788789224176) * 10 ^ 70 +
        7030763335601854169265763725510554340468098685567442046093807593748126) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 146,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (145 - x)) = _
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

private theorem recurrence4Scalar2Exceptional_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (146 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_146 :
    recurrence4Scalar2Exceptional.coeff 146 =
      -((((6747578478385700664127052554634912825535734728835797126381 * 10 ^ 70 +
        8721769838196656398650172564428579740696839916967132903093562794996185) * 10 ^ 70 +
        3734952677165647101441656681559244589621009735103723517168955861872132) * 10 ^ 70 +
        4291577035724409219813960288376511692288966979701360178836611756891794) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 147,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (146 - x)) = _
  rw [show 147 = 1 +
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
  rw [recurrence4Scalar2Exceptional_coeff_146_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (147 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_147 :
    recurrence4Scalar2Exceptional.coeff 147 =
      -((((116315406285393116183291992709843482216570701301613303092456 * 10 ^ 70 +
        9789515346664552254086450464090523197612208037292135251555007062894881) * 10 ^ 70 +
        7998451942644544690944604296191783362587383195407937881661598584849694) * 10 ^ 70 +
        1047859902968006762040908593372264299961051677328531385030708732621423) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 148,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (147 - x)) = _
  rw [show 148 = 2 +
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
  rw [recurrence4Scalar2Exceptional_coeff_147_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (148 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_148 :
    recurrence4Scalar2Exceptional.coeff 148 =
      ((((1389523958021577752941530435538793587762147963023760872355388 * 10 ^ 70 +
        0700521926597204142057680328954592842818549527536528880807554553240553) * 10 ^ 70 +
        5545143229118201431782671091159911644113115355569344349552207816747810) * 10 ^ 70 +
        8237016550558129738449859871118983269485218334704923319379360356843208) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 149,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (148 - x)) = _
  rw [show 149 = 3 +
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
  rw [recurrence4Scalar2Exceptional_coeff_148_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (149 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_149 :
    recurrence4Scalar2Exceptional.coeff 149 =
      -((((10988958344962339193905069122369451123045712303630431261888275 * 10 ^ 70 +
        9082360245691237714694094179884812325646955189269406517303336251429330) * 10 ^ 70 +
        9221289280793648462276800587723416825952117314536844154602056586843122) * 10 ^ 70 +
        6188404311158078427861328687943303989435832630357484130869652308195868) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 150,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (149 - x)) = _
  rw [show 150 = 4 +
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
  rw [recurrence4Scalar2Exceptional_coeff_149_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (150 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_150 :
    recurrence4Scalar2Exceptional.coeff 150 =
      ((((73741124866369259767984670313142164348065851152819547091499808 * 10 ^ 70 +
        5938182496828883246608865031984899188638450434250956504835574745120929) * 10 ^ 70 +
        4583340036572473776968334807034928105551078803805330771167006501503814) * 10 ^ 70 +
        8114276572091036730158672527895847525542326484678514798686663539926431) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 151,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (150 - x)) = _
  rw [show 151 = 5 +
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
  rw [recurrence4Scalar2Exceptional_coeff_150_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (151 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_151 :
    recurrence4Scalar2Exceptional.coeff 151 =
      -((((449387784397366632329993577020984504349341726302244843543751964 * 10 ^ 70 +
        2744929295415266345123588291432857731872994105505189732517669559243281) * 10 ^ 70 +
        7732469644968194524100821897430016334042325401623569056806050799558036) * 10 ^ 70 +
        0740207189228383841407744674399889960810557138647075426545893307438570) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 152,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (151 - x)) = _
  rw [show 152 = 6 +
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
  rw [recurrence4Scalar2Exceptional_coeff_151_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (152 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_152 :
    recurrence4Scalar2Exceptional.coeff 152 =
      ((((2559897981839109983351657731943732789108866502364173583501599998 * 10 ^ 70 +
        7965964571022941878191810086314360082143244729027621460093060408265976) * 10 ^ 70 +
        0279524666824748389439651864968363834754279125483821455446679324641424) * 10 ^ 70 +
        3400470444199969520145510481360807577457376750096552061800555164964327) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 153,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (152 - x)) = _
  rw [show 153 = 7 +
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
  rw [recurrence4Scalar2Exceptional_coeff_152_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (153 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_153 :
    recurrence4Scalar2Exceptional.coeff 153 =
      -((((13838318765829643552605204552511118872863938375366222452956835418 * 10 ^ 70 +
        6745621959533012946858037039347893202705023487088061368623264917120127) * 10 ^ 70 +
        8587425061421776195966468267053328739935050855759634128770685470371383) * 10 ^ 70 +
        7025553898764889282883472444110447078413637145184778990826787340997923) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 154,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (153 - x)) = _
  rw [show 154 = 8 +
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
  rw [recurrence4Scalar2Exceptional_coeff_153_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (154 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_154 :
    recurrence4Scalar2Exceptional.coeff 154 =
      ((((71633645528026717335025515383320099107631216886085172580429771823 * 10 ^ 70 +
        4545248941834817683505092489310212132999557166383286056746149009681816) * 10 ^ 70 +
        9365990145493125635220478722918245423759000720357775898271103086278104) * 10 ^ 70 +
        1835183883673271244083659535578312819351129154959852931367341937805439) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 155,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (154 - x)) = _
  rw [show 155 = 9 +
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
  rw [recurrence4Scalar2Exceptional_coeff_154_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (155 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_155 :
    recurrence4Scalar2Exceptional.coeff 155 =
      -((((357164229850054765672853955116428287127656758541297711166335093200 * 10 ^ 70 +
        0169491335147984621130929092682915106662589919081165878202457051155976) * 10 ^ 70 +
        8551352659414932637840586367302976930521379519536222110411079604915172) * 10 ^ 70 +
        9221630346762235830922082218727254982262455161604363189446846728444938) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 156,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (155 - x)) = _
  rw [show 156 = 10 +
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
  rw [recurrence4Scalar2Exceptional_coeff_155_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (156 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_156 :
    recurrence4Scalar2Exceptional.coeff 156 =
      ((((1722259135545036965485700821697737843982490184934162581007940074447 * 10 ^ 70 +
        6811056538803431677431797528520122182743981085784532096243686402452094) * 10 ^ 70 +
        2668500848265753204204003447219923111333294302033643962990112738422919) * 10 ^ 70 +
        8631385474181592202173712311236115990661462978345812975741522586359462) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 157,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (156 - x)) = _
  rw [show 157 = 11 +
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
  rw [recurrence4Scalar2Exceptional_coeff_156_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (157 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_157 :
    recurrence4Scalar2Exceptional.coeff 157 =
      -((((8055461561816930350060230587872914250993279417105110613501924514269 * 10 ^ 70 +
        3073297390800499263213544292574947330063580556299971065459420836268476) * 10 ^ 70 +
        9955559479253172002778646483485848377534545025996125929074444992243853) * 10 ^ 70 +
        6138818425309348462735893416228424543725933727594806687303324968347757) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 158,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (157 - x)) = _
  rw [show 158 = 12 +
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
  rw [recurrence4Scalar2Exceptional_coeff_157_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (158 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_158 :
    recurrence4Scalar2Exceptional.coeff 158 =
      ((((36627931567446415925870379175426356347695921972229957038783427791321 * 10 ^ 70 +
        1898775168870756515523575930446160305700602681981982010118823711409842) * 10 ^ 70 +
        7045558622201339584077457089787017126463503929545770575674703489402252) * 10 ^ 70 +
        6760298751173509657061469528741749732734958106607110001257733177963418) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 159,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (158 - x)) = _
  rw [show 159 = 13 +
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
  rw [recurrence4Scalar2Exceptional_coeff_158_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (159 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_159 :
    recurrence4Scalar2Exceptional.coeff 159 =
      -((((162188294292405448151619045943957618250051850147926261986054451502848 * 10 ^ 70 +
        1534456939562918056087946659792306774766366924169072012456285884057656) * 10 ^ 70 +
        2869954739844330160867042425559629213419271003734436282659869580804191) * 10 ^ 70 +
        4674414553707042654106624089364379927884863742284796070171192454181862) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 160,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (159 - x)) = _
  rw [show 160 = 14 +
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
  rw [recurrence4Scalar2Exceptional_coeff_159_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (160 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_160 :
    recurrence4Scalar2Exceptional.coeff 160 =
      ((((700350963692292927235116953119812969796164495223207637521014422959219 * 10 ^ 70 +
        0272493403961464829392064644052579945178834176396494807455160029299181) * 10 ^ 70 +
        4016538931501973024857940179283319131294925498287142093719164959115470) * 10 ^ 70 +
        1269405878420326488253527766461772748353930619122122303042531757763654) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 161,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (160 - x)) = _
  rw [show 161 = 15 +
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
  rw [recurrence4Scalar2Exceptional_coeff_160_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (161 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_161 :
    recurrence4Scalar2Exceptional.coeff 161 =
      -((((2952532251417406813919199672273361711740457272815812808169844741859256 * 10 ^ 70 +
        0637997563060357737321714483104106032170593085485080811568792052971119) * 10 ^ 70 +
        9504635598263614385318083236221277259587874592879705257151089194465792) * 10 ^ 70 +
        3455447938307155120138709364823502841760648136965689465686861878206232) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (161 - x)) = _
  rw [show 162 = 16 +
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
  rw [recurrence4Scalar2Exceptional_coeff_161_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (162 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_162 :
    recurrence4Scalar2Exceptional.coeff 162 =
      (((((1 * 10 ^ 70 +
        2163739060476377649190827049754798401534957609548664388042989593974849) * 10 ^ 70 +
        8399344061660895978758876635352406009005711823021385315184395360712861) * 10 ^ 70 +
        4634402508760249658199238239103406226016865601961932360970125906341841) * 10 ^ 70 +
        8173502665298202669607193613266630828922929827067621671741177499263581) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (162 - x)) = _
  rw [show 163 = 17 +
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
  rw [recurrence4Scalar2Exceptional_coeff_162_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (163 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_163 :
    recurrence4Scalar2Exceptional.coeff 163 =
      -(((((4 * 10 ^ 70 +
        9009518814919973647702218408697136128254768462386784387519121600839608) * 10 ^ 70 +
        7657510209451392159980526243946388487219281735630381594968505469597141) * 10 ^ 70 +
        3704160711014890144895610391881957577952628233575420611484086836181978) * 10 ^ 70 +
        2418360111317584460148191615915995550016148895759513599535136356685946) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (163 - x)) = _
  rw [show 164 = 18 +
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
  rw [recurrence4Scalar2Exceptional_coeff_163_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (164 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_164 :
    recurrence4Scalar2Exceptional.coeff 164 =
      (((((19 * 10 ^ 70 +
        3255755805755568321964619687689993685080702664832526841546579735699993) * 10 ^ 70 +
        5909392365587311279763803050927471465853702610358925761155452622123193) * 10 ^ 70 +
        7787746812923047669933654786310944773512172035613368219396061938208404) * 10 ^ 70 +
        6034852014569982126100459083469401485362729695428687607886141210252030) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (164 - x)) = _
  rw [show 165 = 19 +
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
  rw [recurrence4Scalar2Exceptional_coeff_164_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (165 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_165 :
    recurrence4Scalar2Exceptional.coeff 165 =
      -(((((74 * 10 ^ 70 +
        6244912814153207939166767276649666369462014288396761090131825656314390) * 10 ^ 70 +
        0484328633290945420809144089938097833753532861829383262298387909637546) * 10 ^ 70 +
        7480206837548950212938853884521903391702991244389887183036853926003808) * 10 ^ 70 +
        8995043428369492258039253871207128102072309572815158307083472247213423) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (165 - x)) = _
  rw [show 166 = 20 +
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
  rw [recurrence4Scalar2Exceptional_coeff_165_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (166 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_166 :
    recurrence4Scalar2Exceptional.coeff 166 =
      (((((282 * 10 ^ 70 +
        3278371783672948558440410806241948679515803594928100197463513877244875) * 10 ^ 70 +
        9508025098745724312445380816859995746611754666826419643408633302435049) * 10 ^ 70 +
        1166614821521169848298820728731758681302425464235276499254603803021651) * 10 ^ 70 +
        5896547139538353751916537970453167239588081766900969789917996587731543) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (166 - x)) = _
  rw [show 167 = 21 +
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
  rw [recurrence4Scalar2Exceptional_coeff_166_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (167 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_167 :
    recurrence4Scalar2Exceptional.coeff 167 =
      -(((((1047 * 10 ^ 70 +
        0073625659785096636694516858936430928563169810965533606217585898574106) * 10 ^ 70 +
        4767338013895144320148357122588553676483191267717743103306168248856819) * 10 ^ 70 +
        0594183905912587543816820865824147125755969911947853496301680668813232) * 10 ^ 70 +
        7747433094364067302439963824008936455206077744725664642339245624366635) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (167 - x)) = _
  rw [show 168 = 22 +
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
  rw [recurrence4Scalar2Exceptional_coeff_167_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (168 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_168 :
    recurrence4Scalar2Exceptional.coeff 168 =
      (((((3807 * 10 ^ 70 +
        5729388105632386429635630372500517596761234887584439237081148353254255) * 10 ^ 70 +
        0696800221374688617803351714274265791517661417566170729601993100338513) * 10 ^ 70 +
        0412433223907696388114512298524358901521465938549865651288620691179286) * 10 ^ 70 +
        8615886495320057233370954176215983181190696407532184500471541112637380) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (168 - x)) = _
  rw [show 169 = 23 +
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
  rw [recurrence4Scalar2Exceptional_coeff_168_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (169 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_169 :
    recurrence4Scalar2Exceptional.coeff 169 =
      -(((((13583 * 10 ^ 70 +
        4424579556015367743350623456487396137357980925630456254950693281823533) * 10 ^ 70 +
        2316835539905878783424153063409543322286197697241746531391926086975646) * 10 ^ 70 +
        1400103747962177572347713426488900241975310340680018806058079948846280) * 10 ^ 70 +
        3982036360470028784336275927100101584356162936682574217789245448589007) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (169 - x)) = _
  rw [show 170 = 24 +
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
  rw [recurrence4Scalar2Exceptional_coeff_169_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (170 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_170 :
    recurrence4Scalar2Exceptional.coeff 170 =
      (((((47553 * 10 ^ 70 +
        2220994723261192011692887853339704573680505875829218050542356277562913) * 10 ^ 70 +
        9218512678045580667247258863456900415163810287798390041073642605387529) * 10 ^ 70 +
        8741538943289003306708330920975340098897385576261250249369840255378242) * 10 ^ 70 +
        3965949166934063983357155836326589778684802775582200577507239009376763) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (170 - x)) = _
  rw [show 171 = 25 +
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
  rw [recurrence4Scalar2Exceptional_coeff_170_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (171 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_171 :
    recurrence4Scalar2Exceptional.coeff 171 =
      -(((((163414 * 10 ^ 70 +
        6004053180166700852612354139335643410055316199703796973310610974031049) * 10 ^ 70 +
        9879895821765674746153260658143836705620596759672654740049882158317405) * 10 ^ 70 +
        0573240814162563755516716703156378230621442605706193247027349709385313) * 10 ^ 70 +
        9608354891012069593990838037795763218925065067322036468380624001842070) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (171 - x)) = _
  rw [show 172 = 26 +
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
  rw [recurrence4Scalar2Exceptional_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (172 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_172 :
    recurrence4Scalar2Exceptional.coeff 172 =
      (((((551396 * 10 ^ 70 +
        0703895529524587799773634977507865573411059695803474757728793339129217) * 10 ^ 70 +
        7685198737419972888176657669745866774700288952652130971335698673586794) * 10 ^ 70 +
        7119555004691952230287920251258105611687103064816435950491288930544139) * 10 ^ 70 +
        0825908523667952532951917355783753103705099914663548037386443981698531) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (172 - x)) = _
  rw [show 173 = 27 +
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
  rw [recurrence4Scalar2Exceptional_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (173 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_173 :
    recurrence4Scalar2Exceptional.coeff 173 =
      -(((((1827299 * 10 ^ 70 +
        5734634264984774300750296381285628831639769087230226114024718496199261) * 10 ^ 70 +
        9260756396416742038321997943867006540811771302335829427311275426440190) * 10 ^ 70 +
        6726267797386846821782920458974282903156508461473241315360262524082711) * 10 ^ 70 +
        0281450409469535502840286801337317142598927695359895636278175388988459) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (173 - x)) = _
  rw [show 174 = 28 +
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
  rw [recurrence4Scalar2Exceptional_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (174 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_174 :
    recurrence4Scalar2Exceptional.coeff 174 =
      (((((5948836 * 10 ^ 70 +
        0575136993967327713928513665666437166535284530424358195512018010901178) * 10 ^ 70 +
        9927122372702913091408098291218235838289481083657165044539607604754579) * 10 ^ 70 +
        6304218670289311021783125313467302726414936875698395661343979775615378) * 10 ^ 70 +
        0451494513671293198798531305744287243627868721296422314029813433056568) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (174 - x)) = _
  rw [show 175 = 29 +
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
  rw [recurrence4Scalar2Exceptional_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (175 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_175 :
    recurrence4Scalar2Exceptional.coeff 175 =
      -(((((19029432 * 10 ^ 70 +
        7057053502472431358669866419124279125143535448803784323117137103218008) * 10 ^ 70 +
        7506510315719996097340358577134331390309710837036529279832712725515953) * 10 ^ 70 +
        3435362414895130125650788450487552021309048215786472894503114186262357) * 10 ^ 70 +
        8024551461840622121177031574613569781590893831648726277757243733435304) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (175 - x)) = _
  rw [show 176 = 30 +
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
  rw [recurrence4Scalar2Exceptional_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (176 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_176 :
    recurrence4Scalar2Exceptional.coeff 176 =
      (((((59824643 * 10 ^ 70 +
        9014127613439362602996511784313605796887616695828797061625774295779911) * 10 ^ 70 +
        6000739631479282634429144980920580396407101145399635140756818890830411) * 10 ^ 70 +
        7385267157814157175786512958574064423018811076789043072160840819918571) * 10 ^ 70 +
        2947987048509576346604698056786523124410427429061009417220675213956146) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (176 - x)) = _
  rw [show 177 = 31 +
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
  rw [recurrence4Scalar2Exceptional_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (177 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_177 :
    recurrence4Scalar2Exceptional.coeff 177 =
      -(((((184874851 * 10 ^ 70 +
        1397560954452565045602231282545624862743884740453793652108854910671543) * 10 ^ 70 +
        1611462456822520716822006854717282488795303037204820519998573041396229) * 10 ^ 70 +
        7527160284864705631309169510941810621991223159521811466295435654253945) * 10 ^ 70 +
        6786961978350647113539403952496816537543835792433845588209707898473808) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (177 - x)) = _
  rw [show 178 = 32 +
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
  rw [recurrence4Scalar2Exceptional_coeff_177_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (178 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_178 :
    recurrence4Scalar2Exceptional.coeff 178 =
      (((((561690082 * 10 ^ 70 +
        5753439799514767594413001478968882328187400407965206943143454406038529) * 10 ^ 70 +
        6736640503751373799891069034898284849582682639141583752417981347333672) * 10 ^ 70 +
        9136146927863241164601761823738346272451902040123184702299139564982730) * 10 ^ 70 +
        1447721322995461645203162231630115821687245564175385389877382233863470) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (178 - x)) = _
  rw [show 179 = 33 +
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
  rw [recurrence4Scalar2Exceptional_coeff_178_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (179 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_179 :
    recurrence4Scalar2Exceptional.coeff 179 =
      -(((((1678069550 * 10 ^ 70 +
        1217977835117642974628362923987882545013015830005741356716812415201180) * 10 ^ 70 +
        0712462090676044977764278702919023055575660876962835209525579555606312) * 10 ^ 70 +
        6003668606347342359621607168723799963762061255824941594785456883962942) * 10 ^ 70 +
        5887126239437383897080727599700613677251020537195706790314303884684254) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (179 - x)) = _
  rw [show 180 = 34 +
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
  rw [recurrence4Scalar2Exceptional_coeff_179_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (180 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_180 :
    recurrence4Scalar2Exceptional.coeff 180 =
      (((((4930446955 * 10 ^ 70 +
        7528034215561882967993344203594773107281223610822219048955825084843457) * 10 ^ 70 +
        3689307978798681775554397091078186244159779037862920475518375926095811) * 10 ^ 70 +
        4886262717855415582592439009027085522310691327346041593052347982688091) * 10 ^ 70 +
        3658301984094967170235891136904759425906809495503331250445069155793661) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (180 - x)) = _
  rw [show 181 = 35 +
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
  rw [recurrence4Scalar2Exceptional_coeff_180_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (181 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_181 :
    recurrence4Scalar2Exceptional.coeff 181 =
      -(((((14249209752 * 10 ^ 70 +
        3373362824966456488137290064891093891402138692311654979631656372976129) * 10 ^ 70 +
        9681131063173580988134432866708437633824993441836782800015701991990585) * 10 ^ 70 +
        9064088691187621494072108452997542210563991420209998011881234442360103) * 10 ^ 70 +
        4264608765953278712942073357541043346678034556362053316336300777887404) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (181 - x)) = _
  rw [show 182 = 36 +
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
  rw [recurrence4Scalar2Exceptional_coeff_181_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (182 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_182 :
    recurrence4Scalar2Exceptional.coeff 182 =
      (((((40512119359 * 10 ^ 70 +
        8033352495717418610497701271167621601464892946295378027860022910472446) * 10 ^ 70 +
        2981173889023139472011302850658098685410572990986438442191460143204851) * 10 ^ 70 +
        1844163128098220592384199411768614297858537146103788884315837786452958) * 10 ^ 70 +
        4153514613450980197251558529969683740048645556478239778105530714777363) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (182 - x)) = _
  rw [show 183 = 37 +
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
  rw [recurrence4Scalar2Exceptional_coeff_182_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (183 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_183 :
    recurrence4Scalar2Exceptional.coeff 183 =
      -(((((113325385970 * 10 ^ 70 +
        4191160573050371853531942877904284529173668586978628626064313452852899) * 10 ^ 70 +
        8109579192769651805398769334175260127052172601797556055153727037993666) * 10 ^ 70 +
        6608155089120149256036263975150700923257162529273106463902272338235396) * 10 ^ 70 +
        1647384871867467286794497050338295530675110185849668802639008333053225) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (183 - x)) = _
  rw [show 184 = 38 +
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
  rw [recurrence4Scalar2Exceptional_coeff_183_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (184 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_184 :
    recurrence4Scalar2Exceptional.coeff 184 =
      (((((311941361350 * 10 ^ 70 +
        9665044890489994019514032533671295078128431632100543998400522241899116) * 10 ^ 70 +
        4778541271433006276861306512813691495456851122250256518332292482766762) * 10 ^ 70 +
        0691845405158271011659100704766251558131548873952679321153853031802780) * 10 ^ 70 +
        9449712666874256364508388099714040104071226451204711763818795472698311) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (184 - x)) = _
  rw [show 185 = 39 +
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
  rw [recurrence4Scalar2Exceptional_coeff_184_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (185 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_185 :
    recurrence4Scalar2Exceptional.coeff 185 =
      -(((((845035611255 * 10 ^ 70 +
        9571759636564688227554404327374923563366391351865535275351165580220501) * 10 ^ 70 +
        4168487966165052983353964941426724301679119778857531461505804971938038) * 10 ^ 70 +
        2903897766979820107906998342930308843187283256487389750605987010646921) * 10 ^ 70 +
        5364456300769966002862595656120183466030519820168855920362076559368145) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (185 - x)) = _
  rw [show 186 = 40 +
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
  rw [recurrence4Scalar2Exceptional_coeff_185_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (186 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_186 :
    recurrence4Scalar2Exceptional.coeff 186 =
      (((((2253116580848 * 10 ^ 70 +
        0804796284222044334732533544680367858534793123983383244913712832064302) * 10 ^ 70 +
        8171967804926376691165693163074983897269337001411892580726243040075160) * 10 ^ 70 +
        7160866049530463901250771925216965163074637284594082069308920405126033) * 10 ^ 70 +
        5639903000732771483387439876201610037952500299948310919693119650988331) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (186 - x)) = _
  rw [show 187 = 41 +
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
  rw [recurrence4Scalar2Exceptional_coeff_186_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (187 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_187 :
    recurrence4Scalar2Exceptional.coeff 187 =
      -(((((5913531994507 * 10 ^ 70 +
        1051411800948125784827618662502395748863385053694427346549797412365783) * 10 ^ 70 +
        0135994818131020712931283537383490524291000860841007514990928678680633) * 10 ^ 70 +
        7329885334462155614588990740187533682248389578854348957450215614128113) * 10 ^ 70 +
        8426411434283758904333232920129736814285457690511905986724921187729948) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (187 - x)) = _
  rw [show 188 = 42 +
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
  rw [recurrence4Scalar2Exceptional_coeff_187_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (188 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_188 :
    recurrence4Scalar2Exceptional.coeff 188 =
      (((((15279557844530 * 10 ^ 70 +
        5044192487572112627596050386317142997927007157144007885890593864337295) * 10 ^ 70 +
        8707504032977312445154521043202230709785236006192404537665637994095718) * 10 ^ 70 +
        6991195953799082510208612770280537618026474134036472986521091183783263) * 10 ^ 70 +
        0194603865050233784811374788896357128110196990514316415901087538358477) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (188 - x)) = _
  rw [show 189 = 43 +
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
  rw [recurrence4Scalar2Exceptional_coeff_188_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (189 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_189 :
    recurrence4Scalar2Exceptional.coeff 189 =
      -(((((38870409524087 * 10 ^ 70 +
        8455183790389169594979872460490163063922060945963412110331363565687824) * 10 ^ 70 +
        2209465380028367637650419655234448857717199620274571411644861359958115) * 10 ^ 70 +
        3588739659375163486140926114918808026851132721500370642239531863237342) * 10 ^ 70 +
        7622840416702111207569585459105543358875100726291115496016918782858044) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (189 - x)) = _
  rw [show 190 = 44 +
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
  rw [recurrence4Scalar2Exceptional_coeff_189_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (190 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_190 :
    recurrence4Scalar2Exceptional.coeff 190 =
      (((((97367505959319 * 10 ^ 70 +
        0249465205506121076352616072212471456418175399889294362009107206606518) * 10 ^ 70 +
        7680603597066133876390814524294270977199305360966350818158688075475719) * 10 ^ 70 +
        2719846428260629584176544680899628205294953014561346580915584128696233) * 10 ^ 70 +
        3715235289794418365479235814092427292725115712768235736798374874136080) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (190 - x)) = _
  rw [show 191 = 45 +
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
  rw [recurrence4Scalar2Exceptional_coeff_190_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (191 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_191 :
    recurrence4Scalar2Exceptional.coeff 191 =
      -(((((240179515518498 * 10 ^ 70 +
        3969789999719686552979377679996478512750434265712247546317060187637521) * 10 ^ 70 +
        4903266281835743082491959900632981952770324420550729662167035528564129) * 10 ^ 70 +
        7943652126698267158364065156460928349789178577193107484948478139394132) * 10 ^ 70 +
        0741358880475518085455732426032961260003888476289715301714088321732705) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (191 - x)) = _
  rw [show 192 = 46 +
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
  rw [recurrence4Scalar2Exceptional_coeff_191_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (192 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_192 :
    recurrence4Scalar2Exceptional.coeff 192 =
      (((((583476876888254 * 10 ^ 70 +
        7970701436785931047551892914930226406218830756686284716191752431128537) * 10 ^ 70 +
        3791328310566564243675024549301203042758343917370879820332359015220482) * 10 ^ 70 +
        1685932135875065544917917438593348666458806397715783793636053351719241) * 10 ^ 70 +
        9826878955733114622249807080439970415757222858400800851491233805985809) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (192 - x)) = _
  rw [show 193 = 47 +
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
  rw [recurrence4Scalar2Exceptional_coeff_192_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (193 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_193 :
    recurrence4Scalar2Exceptional.coeff 193 =
      -(((((1396093049858785 * 10 ^ 70 +
        7332807988907594767669903790759181169540049585717160794925105478898617) * 10 ^ 70 +
        0752259591688028773410480020242739933235374556289764964309413769167698) * 10 ^ 70 +
        4861057152029494255132542208109948127141594334518652006440596021917694) * 10 ^ 70 +
        8387625784695214685106520779984762170468811474508292791733319185836514) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (193 - x)) = _
  rw [show 194 = 48 +
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
  rw [recurrence4Scalar2Exceptional_coeff_193_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (194 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_194 :
    recurrence4Scalar2Exceptional.coeff 194 =
      (((((3290364023434998 * 10 ^ 70 +
        3256109077922920813215970932778236782333212742812168597032036923779692) * 10 ^ 70 +
        6206383619064233736522913737031824138529873888888212061962528472367961) * 10 ^ 70 +
        5215028541241928829133221787833825706687473510111054850830413261373312) * 10 ^ 70 +
        1452016255276349778148179484277038777176179224284059109936724348596657) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (194 - x)) = _
  rw [show 195 = 49 +
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
  rw [recurrence4Scalar2Exceptional_coeff_194_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (195 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_195 :
    recurrence4Scalar2Exceptional.coeff 195 =
      -(((((7639182577332071 * 10 ^ 70 +
        3413875847034584458023177828523129122782957443279311344249511750388514) * 10 ^ 70 +
        0028860901155959808300645804336699361641837649176135768897792130909654) * 10 ^ 70 +
        2961785657182667940963324970732340919003208479176247607480989758327513) * 10 ^ 70 +
        5408372454370080478881026312200933972121729691777948091614000940856298) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (195 - x)) = _
  rw [show 196 = 50 +
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
  rw [recurrence4Scalar2Exceptional_coeff_195_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (196 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_196 :
    recurrence4Scalar2Exceptional.coeff 196 =
      (((((17472554702459541 * 10 ^ 70 +
        8078117465411929308200751705967492761283809277568798597411186422962758) * 10 ^ 70 +
        6610184124445000069053805703316964769458336272364596640481234787737031) * 10 ^ 70 +
        2147505282554193231410104613874141953449576239576361336224431658081614) * 10 ^ 70 +
        4905973916299277504472489390521014992052316069384213312608188201854775) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (196 - x)) = _
  rw [show 197 = 51 +
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
  rw [recurrence4Scalar2Exceptional_coeff_196_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (197 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_197 :
    recurrence4Scalar2Exceptional.coeff 197 =
      -(((((39373544845347455 * 10 ^ 70 +
        4872398786317164053027303900326725477917969236436141143449823029530933) * 10 ^ 70 +
        0554413673055444633386337638928506003732136247209150193734411052648547) * 10 ^ 70 +
        2983727799967746234141358013084787440642101928300592997145004440626705) * 10 ^ 70 +
        2008297637070095438362373955854598408516012024248141298067824591600083) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (197 - x)) = _
  rw [show 198 = 52 +
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
  rw [recurrence4Scalar2Exceptional_coeff_197_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (198 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_198 :
    recurrence4Scalar2Exceptional.coeff 198 =
      (((((87422269998165601 * 10 ^ 70 +
        2405764538159235256496074127343692401514863809756098750180145504949775) * 10 ^ 70 +
        8650920769212527194018868772205186805516539477958918819342529061024638) * 10 ^ 70 +
        2613716271919863071589440187637381497384908994081011601800024682715205) * 10 ^ 70 +
        7044078928627138441596091926922398268162567663992607094883046789422471) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (198 - x)) = _
  rw [show 199 = 53 +
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
  rw [recurrence4Scalar2Exceptional_coeff_198_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (199 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_199 :
    recurrence4Scalar2Exceptional.coeff 199 =
      -(((((191266483309773926 * 10 ^ 70 +
        1427732510773316758343760440455254964435181170153211364263797721833104) * 10 ^ 70 +
        0425359495736237296862924697346396699754114713563553806499221810525506) * 10 ^ 70 +
        1081350374949204312559042176444399613066664150052034630876012113644872) * 10 ^ 70 +
        0815512159074663866447073847850837584397764382461703696006916446112602) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (199 - x)) = _
  rw [show 200 = 54 +
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
  rw [recurrence4Scalar2Exceptional_coeff_199_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (200 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_200 :
    recurrence4Scalar2Exceptional.coeff 200 =
      (((((412366745973954835 * 10 ^ 70 +
        1544608253364138767913303299017903987479190409500509677893372993242570) * 10 ^ 70 +
        7233560361116756028686490434830863392259749649713287684116495093932245) * 10 ^ 70 +
        4122394680941444706769297077727660600841895011135476530420389845362808) * 10 ^ 70 +
        4823792307669667347506750335223791007325019272042365044632755394695330) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (200 - x)) = _
  rw [show 201 = 55 +
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
  rw [recurrence4Scalar2Exceptional_coeff_200_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (201 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_201 :
    recurrence4Scalar2Exceptional.coeff 201 =
      -(((((876161397180500515 * 10 ^ 70 +
        1810233956261205012357627592764166598011514904328177620293660524915369) * 10 ^ 70 +
        4879384893903073293189899194736311250905021969912319002520230463968305) * 10 ^ 70 +
        8631540784087950091377899227465453450952067661159757250492096112356318) * 10 ^ 70 +
        7019822881275407569778893083223908157120155374773041549069493578955380) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (201 - x)) = _
  rw [show 202 = 56 +
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
  rw [recurrence4Scalar2Exceptional_coeff_201_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (202 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_202 :
    recurrence4Scalar2Exceptional.coeff 202 =
      (((((1834708653533126435 * 10 ^ 70 +
        3575537003466636320292372373828604504298381375739874602135800508557863) * 10 ^ 70 +
        7515268063084367983492293427667597206834490475461963453473544541396029) * 10 ^ 70 +
        3652035955952073408872926054839947648638427139047279063734586945967316) * 10 ^ 70 +
        2335524076340990487328738671268364635452731499004762909824545373579288) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (202 - x)) = _
  rw [show 203 = 57 +
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
  rw [recurrence4Scalar2Exceptional_coeff_202_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (203 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_203 :
    recurrence4Scalar2Exceptional.coeff 203 =
      -(((((3786679183794101214 * 10 ^ 70 +
        8192322025859569949509325550299426221743288301170026119085416064075943) * 10 ^ 70 +
        4530156750185089886155030287221967994745426433216012430867480111479237) * 10 ^ 70 +
        1477022096657105809830591472294569978544858648133417977414880199092055) * 10 ^ 70 +
        4866834949308396038084704725447878410548815202421528728006931188040560) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (203 - x)) = _
  rw [show 204 = 58 +
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
  rw [recurrence4Scalar2Exceptional_coeff_203_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (204 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_204 :
    recurrence4Scalar2Exceptional.coeff 204 =
      (((((7703415908918024110 * 10 ^ 70 +
        1225704521569333988770176819201890567968789055163763868174113228089904) * 10 ^ 70 +
        3765491296385834070810514589666242991960323217082680722634063732620308) * 10 ^ 70 +
        8724609045098352284628088850102173199757960919545556648569534730130257) * 10 ^ 70 +
        5745841382038143029404484892493667468591635107799110690292455223125074) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (204 - x)) = _
  rw [show 205 = 59 +
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
  rw [recurrence4Scalar2Exceptional_coeff_204_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (205 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_205 :
    recurrence4Scalar2Exceptional.coeff 205 =
      -(((((15447770140544397461 * 10 ^ 70 +
        8294891817739709012001617774947726565038306842240141920114626542189529) * 10 ^ 70 +
        3291089476728481293538440837357347470958262733715753651680479717385480) * 10 ^ 70 +
        9816360671370724632381296833137180724486737698850923814494485743166007) * 10 ^ 70 +
        0340169681942791240008402815921071906501739851388083818272927321412500) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (205 - x)) = _
  rw [show 206 = 60 +
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
  rw [recurrence4Scalar2Exceptional_coeff_205_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (206 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_206 :
    recurrence4Scalar2Exceptional.coeff 206 =
      (((((30537202866102705091 * 10 ^ 70 +
        2124977233446543930618657831946419131086473650957277976876238451864875) * 10 ^ 70 +
        6294392288335898031777812805487121368212280156253535965800502048093029) * 10 ^ 70 +
        7556206747926898266863923225610259945334204712662303741376850868164864) * 10 ^ 70 +
        9236444008921046365196901863741585128133608434701842866108867354368801) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (206 - x)) = _
  rw [show 207 = 61 +
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
  rw [recurrence4Scalar2Exceptional_coeff_206_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (207 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_207 :
    recurrence4Scalar2Exceptional.coeff 207 =
      -(((((59510873421759282582 * 10 ^ 70 +
        3361005410898690668518245174836508901890379816942966992997260416184194) * 10 ^ 70 +
        2829759166891700280699417172182247878410137241928860596487266486960278) * 10 ^ 70 +
        9837775667396935712062170411605440057188144219401583738808341284293591) * 10 ^ 70 +
        8992960241255681467979488735736529987685872683623622148284433073038910) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (207 - x)) = _
  rw [show 208 = 62 +
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
  rw [recurrence4Scalar2Exceptional_coeff_207_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (208 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_208 :
    recurrence4Scalar2Exceptional.coeff 208 =
      (((((114337548114450120729 * 10 ^ 70 +
        8044726106054821185211961936456339298121523812800419943344260850453423) * 10 ^ 70 +
        6000703635104881984011995666045480413916913243258455684397205953645186) * 10 ^ 70 +
        0666451454236002678761867581971382845777540854045713583627711862622575) * 10 ^ 70 +
        8269627782698383540969923544294100530293643533446861563735896725222256) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (208 - x)) = _
  rw [show 209 = 63 +
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
  rw [recurrence4Scalar2Exceptional_coeff_208_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (209 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_209 :
    recurrence4Scalar2Exceptional.coeff 209 =
      -(((((216584838848950867003 * 10 ^ 70 +
        7654849651449460310551444607166173206040648764267288189303843853188074) * 10 ^ 70 +
        5240584173484915485364481081449458273143826544779270408811779165024429) * 10 ^ 70 +
        7989608635672937822322142548530375479275458832777224968492190742771626) * 10 ^ 70 +
        9987496779277418886064428184776068377876616848876946476841443139267945) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (209 - x)) = _
  rw [show 210 = 64 +
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
  rw [recurrence4Scalar2Exceptional_coeff_209_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (210 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_210 :
    recurrence4Scalar2Exceptional.coeff 210 =
      (((((404514699503874873523 * 10 ^ 70 +
        7065414389852701494214319254650536166862477675449252081353748993231392) * 10 ^ 70 +
        4014157536276918171616809525761850868102780524873471337013429040408676) * 10 ^ 70 +
        3167360336888015819822213185127838304695715568050947176585493411613782) * 10 ^ 70 +
        2625053689552383755960499056819389332179549540117724743293363418124316) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (210 - x)) = _
  rw [show 211 = 65 +
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
  rw [recurrence4Scalar2Exceptional_coeff_210_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (211 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_211 :
    recurrence4Scalar2Exceptional.coeff 211 =
      -(((((744950507053642060924 * 10 ^ 70 +
        5039211596043914128745892129317678409136791136970874534972157470853798) * 10 ^ 70 +
        5609183534892182734558620998968540972916498404039252500445700016138348) * 10 ^ 70 +
        0491430438892143658619036255804268695988779868175560844785437810518885) * 10 ^ 70 +
        2661695542984562381572249702722509350883869468115891267426726494626649) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (211 - x)) = _
  rw [show 212 = 66 +
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
  rw [recurrence4Scalar2Exceptional_coeff_211_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (212 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_212 :
    recurrence4Scalar2Exceptional.coeff 212 =
      (((((1352777950412606821288 * 10 ^ 70 +
        1205266348296405519827166576122724596032589583055892213333267050701255) * 10 ^ 70 +
        2894920495484141941013357570380017390604771777828034965986450302428960) * 10 ^ 70 +
        4863675016301288568264946094628555454059800266280101364142260529428216) * 10 ^ 70 +
        5759495996651051301205945287748483949684140271465132134341606342890997) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (212 - x)) = _
  rw [show 213 = 67 +
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
  rw [recurrence4Scalar2Exceptional_coeff_212_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (213 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_213 :
    recurrence4Scalar2Exceptional.coeff 213 =
      -(((((2422423608753774171721 * 10 ^ 70 +
        6614650193462622237078165755193164513948228166008212867131332903061881) * 10 ^ 70 +
        1638572850140344173603287533028190221638913421585778125515721563838375) * 10 ^ 70 +
        8663037354282525394543780229168245534629758827395498814594240529197888) * 10 ^ 70 +
        0516941971423458324074926533493878713158353644749644298614840127721211) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (213 - x)) = _
  rw [show 214 = 68 +
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
  rw [recurrence4Scalar2Exceptional_coeff_213_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (214 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_214 :
    recurrence4Scalar2Exceptional.coeff 214 =
      (((((4277756164851042049642 * 10 ^ 70 +
        3851241068580839670592695377231653465602854230348960625021063124659646) * 10 ^ 70 +
        4630955055903146718014490324713153015848988386506081072628360433087866) * 10 ^ 70 +
        3290806636473542321077314363319287152056018226658363332036193647517465) * 10 ^ 70 +
        4508005046892994095980318968449252560443956431608773383427056995946386) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (214 - x)) = _
  rw [show 215 = 69 +
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
  rw [recurrence4Scalar2Exceptional_coeff_214_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (215 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_215 :
    recurrence4Scalar2Exceptional.coeff 215 =
      -(((((7449748447460810465905 * 10 ^ 70 +
        7068056159253777287554822505354285391116964430416156160500659059327409) * 10 ^ 70 +
        9606593252815055258142252583181480898435485216344350697479592879471804) * 10 ^ 70 +
        8281536379564837209696284111009473907107882386719801184768851163976626) * 10 ^ 70 +
        9555790796690308624342476658376314089524744372488729217385708779613908) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (215 - x)) = _
  rw [show 216 = 70 +
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
  rw [recurrence4Scalar2Exceptional_coeff_215_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (216 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_216 :
    recurrence4Scalar2Exceptional.coeff 216 =
      (((((12795095885959051515724 * 10 ^ 70 +
        7543868106698633904217777535291279191228472575851132604118824023622862) * 10 ^ 70 +
        3685087374751892929736336870267036117998666464608606547780197231608501) * 10 ^ 70 +
        5927176785022731261175802320391235401678117128978831138526486213983113) * 10 ^ 70 +
        8383113247839131712557101986843561632186350149202499187519915950945824) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (216 - x)) = _
  rw [show 217 = 71 +
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
  rw [recurrence4Scalar2Exceptional_coeff_216_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (217 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_217 :
    recurrence4Scalar2Exceptional.coeff 217 =
      -(((((21673945552510217475598 * 10 ^ 70 +
        4664508167040169037358978970699141039038891568834439771502121581656883) * 10 ^ 70 +
        2971709228223263152799321142559968228958725343589033503359333576236548) * 10 ^ 70 +
        4773639145306230637400486490808201084196422446996247876432907756073946) * 10 ^ 70 +
        7063762520382075581067463143991190985310617402725031314868297991784577) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (217 - x)) = _
  rw [show 218 = 72 +
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
  rw [recurrence4Scalar2Exceptional_coeff_217_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (218 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_218 :
    recurrence4Scalar2Exceptional.coeff 218 =
      (((((36210998560762794532764 * 10 ^ 70 +
        3918250143612486724144382951717112709805246002057124505374728760166352) * 10 ^ 70 +
        6324252519737862816318328666382452443484637844379197608066442773638793) * 10 ^ 70 +
        2403534530790537008724902329902545313002550973414176270080366243566763) * 10 ^ 70 +
        8558371253035398553004368250192329126165320689943362936553281586187467) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (218 - x)) = _
  rw [show 219 = 73 +
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
  rw [recurrence4Scalar2Exceptional_coeff_218_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar2Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C2_coeff_high (219 - x) (by
    omega)]
  norm_num

theorem recurrence4Scalar2Exceptional_coeff_219 :
    recurrence4Scalar2Exceptional.coeff 219 =
      -(((((59671392308471724340286 * 10 ^ 70 +
        2234883150005085166444582348137203716464303732367091062774675969683184) * 10 ^ 70 +
        7058920177629572457366378167598181832057953072331177606133958454530546) * 10 ^ 70 +
        4274125789240941540641738368286554231982770074099513093615050734934122) * 10 ^ 70 +
        9533648602111968962455140566132667324739090793140531448081030393183529) : ℚ) := by
  unfold recurrence4Scalar2Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient2.coeff (219 - x)) = _
  rw [show 220 = 74 +
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
  rw [recurrence4Scalar2Exceptional_coeff_219_prefix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
