/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar2LeftPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar2Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
