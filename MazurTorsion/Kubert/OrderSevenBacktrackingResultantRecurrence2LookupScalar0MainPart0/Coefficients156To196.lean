/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0MainPart0Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B0_coeff_0
  recurrence2B0_coeff_1
  recurrence2B0_coeff_2
  recurrence2B0_coeff_3
  recurrence2B0_coeff_4
  recurrence2B0_coeff_5
  recurrence2B0_coeff_6
  recurrence2B0_coeff_7
  recurrence2B0_coeff_8
  recurrence2B0_coeff_9
  recurrence2B0_coeff_10
  recurrence2B0_coeff_11
  recurrence2B0_coeff_12
  recurrence2B0_coeff_13
  recurrence2B0_coeff_14
  recurrence2B0_coeff_15
  recurrence2B0_coeff_16
  recurrence2B0_coeff_17
  recurrence2B0_coeff_18
  recurrence2B0_coeff_19
  recurrence2B0_coeff_20
  recurrence2B0_coeff_21
  recurrence2B0_coeff_22
  recurrence2B0_coeff_23
  recurrence2B0_coeff_24
  recurrence2B0_coeff_25
  recurrence2B0_coeff_26
  recurrence2B0_coeff_27
  recurrence2B0_coeff_28
  recurrence2B0_coeff_29
  recurrence2B0_coeff_30
  recurrence2B0_coeff_31
  recurrence2B0_coeff_32
  recurrence2B0_coeff_33
  recurrence2B0_coeff_34
  recurrence2B0_coeff_35
  recurrence2B0_coeff_36
  recurrence2B0_coeff_37
  recurrence2B0_coeff_38
  recurrence2B0_coeff_39
  recurrence2B0_coeff_40
  recurrence2B0_coeff_41
  recurrence2B0_coeff_42
  recurrence2B0_coeff_43
  recurrence2B0_coeff_44
  recurrence2B0_coeff_45
  recurrence2B0_coeff_46
  recurrence2B0_coeff_47
  recurrence2B0_coeff_48
  recurrence2B0_coeff_49
  recurrence2B0_coeff_50
  recurrence2B0_coeff_51
  recurrence2B0_coeff_52
  recurrence2B0_coeff_53
  recurrence2B0_coeff_54
  recurrence2B0_coeff_55
  recurrence2B0_coeff_56
  recurrence2B0_coeff_57
  recurrence2B0_coeff_58
  recurrence2B0_coeff_59
  recurrence2B0_coeff_60
  recurrence2B0_coeff_61
  recurrence2B0_coeff_62
  recurrence2B0_coeff_63
  recurrence2B0_coeff_64
  recurrence2B0_coeff_65
  recurrence2B0_coeff_66
  recurrence2B0_coeff_67
  recurrence2B0_coeff_68
  recurrence2B0_coeff_69
  recurrence2B0_coeff_70
  recurrence2B0_coeff_71
  recurrence2B0_coeff_72
  recurrence2B0_coeff_73
  recurrence2B0_coeff_74
  recurrence2B0_coeff_75
  recurrence2B0_coeff_76
  recurrence2B0_coeff_77
  recurrence2B0_coeff_78
  recurrence2B0_coeff_79
  recurrence2B0_coeff_80
  recurrence2B0_coeff_81
  recurrence2B0_coeff_82
  recurrence2B0_coeff_83
  recurrence2B0_coeff_84
  recurrence2B0_coeff_85
  recurrence2B0_coeff_86
  recurrence2B0_coeff_87
  recurrence2B0_coeff_88
  recurrence2B0_coeff_89
  recurrence2B0_coeff_90
  recurrence2B0_coeff_91
  recurrence2B0_coeff_92
  recurrence2B0_coeff_93
  recurrence2B0_coeff_94
  recurrence2B0_coeff_95
  recurrence2B0_coeff_96
  recurrence2B0_coeff_97
  recurrence2B0_coeff_98
  recurrence2B0_coeff_99
  recurrence2B0_coeff_100
  recurrence2B0_coeff_101
  recurrence2B0_coeff_102
  recurrence2B0_coeff_103
  recurrence2B0_coeff_104
  recurrence2B0_coeff_105
  recurrence2B0_coeff_106
  recurrence2B0_coeff_107
  recurrence2B0_coeff_108
  recurrence2B0_coeff_109
  recurrence2B0_coeff_110
  recurrence2B0_coeff_111
  recurrence2B0_coeff_112
  recurrence2B0_coeff_113
  recurrence2B0_coeff_114
  recurrence2B0_coeff_115
  recurrence2B0_coeff_116
  recurrence2B0_coeff_117
  recurrence2B0_coeff_118
  recurrence2B0_coeff_119
  recurrence2B0_coeff_120
  recurrence2B0_coeff_121
  recurrence2B0_coeff_122
  recurrence2B0_coeff_123
  recurrence2B0_coeff_124
  recurrence2B0_coeff_125
  recurrence2B0_coeff_126
  recurrence2B0_coeff_127
  recurrence2B0_coeff_128
  recurrence2B0_coeff_129
  recurrence2B0_coeff_130
  recurrence2B0_coeff_131
  recurrence2B0_coeff_132
  recurrence2B0_coeff_133
  recurrence2B0_coeff_134
  recurrence2B0_coeff_135
  recurrence2B0_coeff_136
  recurrence2B0_coeff_137
  recurrence2B0_coeff_138
  recurrence2B0_coeff_139
  recurrence2B0_coeff_140
  recurrence2B0_coeff_141
  recurrence2B0_coeff_142
  recurrence2B0_coeff_143
  recurrence2B0_coeff_144
  recurrence2B0_coeff_145
  recurrence2B0_coeff_146
  recurrence2B0_coeff_147
  recurrence2B0_coeff_148
  recurrence2B0_coeff_149
  recurrence2B0_coeff_150
  recurrence2B0_coeff_151
  recurrence2B0_coeff_152
  recurrence2B0_coeff_153
  recurrence2B0_coeff_154
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

private theorem recurrence2Scalar0Main_coeff_156_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (156 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_156 :
    recurrence2Scalar0Main.coeff 156 =
      (((39197138570117565323848036944882767882671532 * 10 ^ 70 +
        7552057296698648401090094975882700382620079493699596907266519533614196) * 10 ^ 70 +
        3253215702681637850040692837120788248507672518028837295418159343076337) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 29 = 27 +
      2 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_156_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_157_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (157 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_157 :
    recurrence2Scalar0Main.coeff 157 =
      -(((37805421813751138082677481914555069479577610 * 10 ^ 70 +
        3516487852657959092868053533891970900524109797732402628669228623019376) * 10 ^ 70 +
        6807689166758577424531534409556657350303616118922438801183867428173853) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 30 = 27 +
      3 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_157_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_158_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (158 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_158 :
    recurrence2Scalar0Main.coeff 158 =
      -(((334191990342574529351672446349447855277155506 * 10 ^ 70 +
        8184174720959962652331138240412812586264505513998577966230187738213776) * 10 ^ 70 +
        1568509333816093324316273225331906744684322085582248879349509279761219) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 31 = 27 +
      4 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_158_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_159_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (159 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_159 :
    recurrence2Scalar0Main.coeff 159 =
      (((1692414095037027696147777090904205591065652269 * 10 ^ 70 +
        8101397403079117835292192667896336909251753880736970634039275825174414) * 10 ^ 70 +
        6981356780059748480993332140183928077709776166643877224400505875784958) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 32 = 27 +
      5 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_159_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_160_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (160 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_160 :
    recurrence2Scalar0Main.coeff 160 =
      -(((2338424402035940931145277779767586034559389504 * 10 ^ 70 +
        2959591680923880139348625656268426249925877855089690488251044549341572) * 10 ^ 70 +
        8322614450188856907358444182860349406253456174629139882421553237298256) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 33 = 27 +
      6 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_160_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (161 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_161 :
    recurrence2Scalar0Main.coeff 161 =
      -(((10959483461202649376950684197556612719146955358 * 10 ^ 70 +
        7477927664823048327270749154028440140182992990240209511774927271201990) * 10 ^ 70 +
        4036047762898392222125355301894920354746216632339077413874293362214234) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 34 = 27 +
      7 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (162 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_162 :
    recurrence2Scalar0Main.coeff 162 =
      (((67073363271447596063042935402102845643066331753 * 10 ^ 70 +
        2720264619180036567038891118678831166551900269330957000869991568668015) * 10 ^ 70 +
        7838633717544357694671759044747621746394725924207932101618436534967452) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 35 = 27 +
      8 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (163 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_163 :
    recurrence2Scalar0Main.coeff 163 =
      -(((123092222785154814071731459378141257604229197750 * 10 ^ 70 +
        7722719056738823125236286413235888547582978717364743637485394580318380) * 10 ^ 70 +
        1917951983145523937414642528977708832761881913901938439629347623766549) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 36 = 27 +
      9 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (164 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_164 :
    recurrence2Scalar0Main.coeff 164 =
      -(((297347492933049515868767861574850746391211058674 * 10 ^ 70 +
        5883641913562796113345500455238223201210306825716112968141274672777428) * 10 ^ 70 +
        3454134713742411419629727231984064416392212898378526885584620701657997) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 37 = 27 +
      10 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (165 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_165 :
    recurrence2Scalar0Main.coeff 165 =
      (((2474985576145966320892800214919965428367192727845 * 10 ^ 70 +
        4510939968143109923071211509443585760862393794214843936174218110396099) * 10 ^ 70 +
        2762762163516778023894044673302496059902363515717726516745516622763855) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 38 = 27 +
      11 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (166 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_166 :
    recurrence2Scalar0Main.coeff 166 =
      -(((5996848089597615248344340503548537060776847376666 * 10 ^ 70 +
        5208850893535485044382690929373928040705764455341144900735878929968546) * 10 ^ 70 +
        7138587171087656744598901876269698793566346292301985162284135397382184) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 39 = 27 +
      12 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (167 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_167 :
    recurrence2Scalar0Main.coeff 167 =
      -(((4302354516744625145600216012570234490720820426014 * 10 ^ 70 +
        6245034189686168346918233092849155860603106233416615067646878008262850) * 10 ^ 70 +
        8533314633175097091517412591135453673062919428555740345329697435148874) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 40 = 27 +
      13 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (168 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_168 :
    recurrence2Scalar0Main.coeff 168 =
      (((80641698921825460412574517508610335063071964953941 * 10 ^ 70 +
        0098905577641039457594113874471644937404023600279948522172721114746786) * 10 ^ 70 +
        3456105073327536201207550481805684099691369911800843281168986982918225) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 41 = 27 +
      14 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (169 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_169 :
    recurrence2Scalar0Main.coeff 169 =
      -(((262119636564694449919105053319183461793507790919410 * 10 ^ 70 +
        3873567123580988730724764126163730846340612716051090860752651290946076) * 10 ^ 70 +
        3692897699335704497907094398942527636224286487829150471212903229749093) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 42 = 27 +
      15 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (170 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_170 :
    recurrence2Scalar0Main.coeff 170 =
      (((166327185542396279077546870536183783924359182985734 * 10 ^ 70 +
        1743556792873227543954508882989767713153740384122283948743341739606723) * 10 ^ 70 +
        4935503841965829814530016810064105726922116484152230532321629264736314) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 43 = 27 +
      16 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (171 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_171 :
    recurrence2Scalar0Main.coeff 171 =
      (((2035637842175068793200489428813650978438211093495375 * 10 ^ 70 +
        4854734782045805019216959993146134236483089997802286828656966441599483) * 10 ^ 70 +
        1540238757596498871114789733833958019802790480745372787351310009960864) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 44 = 27 +
      17 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (172 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_172 :
    recurrence2Scalar0Main.coeff 172 =
      -(((9505350815303114524356427404095592218656563921471295 * 10 ^ 70 +
        0658315292202738638305995783616213915275237205392193168672576308495734) * 10 ^ 70 +
        7889826059041103216540485203741563165832689934439430707655399381737638) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 45 = 27 +
      18 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (173 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_173 :
    recurrence2Scalar0Main.coeff 173 =
      (((16649361649219824736172836606134145131482112747926864 * 10 ^ 70 +
        5776946898815623340141165474235646984604623456295049487375027988877399) * 10 ^ 70 +
        1046569311421143975693043038782218211046152762165789188517701289280011) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 46 = 27 +
      19 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (174 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_174 :
    recurrence2Scalar0Main.coeff 174 =
      (((27376178452013420151568963686118878994991134843190835 * 10 ^ 70 +
        7494584327039127147990916119505629371144508213050515820034002869369878) * 10 ^ 70 +
        0643933025951533891375487870279715014905408051332051416822602644145602) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 47 = 27 +
      20 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (175 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_175 :
    recurrence2Scalar0Main.coeff 175 =
      -(((262960639522632646064182993228324560072139515144528049 * 10 ^ 70 +
        6594343979137061376405840523825703568902392780467699532091567291846985) * 10 ^ 70 +
        5337252031958063982997952760716004477936121546569934227812496826467449) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 48 = 27 +
      21 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (176 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_176 :
    recurrence2Scalar0Main.coeff 176 =
      (((759817087602437887095844298798138273640028418113298930 * 10 ^ 70 +
        2862998712143574640572476870538565476061873478652353450956149333635861) * 10 ^ 70 +
        8026132656380324103116441526863732791662853463463093560621281078191839) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 49 = 27 +
      22 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (177 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_177 :
    recurrence2Scalar0Main.coeff 177 =
      -(((533112987945108319488141230587210041923187710232575675 * 10 ^ 70 +
        7235983200647992657989101169583388402232592526730432962829272448013929) * 10 ^ 70 +
        6064820538644076400400857769141872191053879860359726395330344995324186) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 50 = 27 +
      23 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (178 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_178 :
    recurrence2Scalar0Main.coeff 178 =
      -(((4743712558315898378476974815138076580285080484977591548 * 10 ^ 70 +
        5529857080688125337995463847119373451270480233901586467074400580342998) * 10 ^ 70 +
        1077699923836994327723986039232547844116388584583880789281091927790559) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (179 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_179 :
    recurrence2Scalar0Main.coeff 179 =
      (((22957629966697309131896505671166623872759920954193202484 * 10 ^ 70 +
        0049068067076291936536779634923609794931626535315152554698573566043225) * 10 ^ 70 +
        2902134818697249909185168202340848083230306389779759115087379592249405) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 52 = 27 +
      25 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (180 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_180 :
    recurrence2Scalar0Main.coeff 180 =
      -(((47418429562099132364740337146993945721949998209322085117 * 10 ^ 70 +
        0380660001645753643977486197615348294785386480667382926095340642563487) * 10 ^ 70 +
        8475489564979586281643353991145723033851533866119811245044238551846475) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 53 = 27 +
      26 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (181 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_181 :
    recurrence2Scalar0Main.coeff 181 =
      -(((12530532955639367192851096163283833930215969203608890713 * 10 ^ 70 +
        2906754836117778558039774408678000810621962734651508350780691854705000) * 10 ^ 70 +
        0448378560572029496812785319549106602932020204652952544222429895387827) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 54 = 27 +
      27 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (182 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_182 :
    recurrence2Scalar0Main.coeff 182 =
      (((445274086917182776301435001771415815938782119142796620408 * 10 ^ 70 +
        9979808463727908959128157674870307256623117303850326604673293420747139) * 10 ^ 70 +
        5967621258867479049045866239647105770980203934069208431851437747907517) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 55 = 27 +
      28 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (183 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_183 :
    recurrence2Scalar0Main.coeff 183 =
      -(((1616430093132563654934547069932333170194316750066542104867 * 10 ^ 70 +
        2825613165480009655038045535531503859937310214625025710030441769003283) * 10 ^ 70 +
        6627798945795720422234857243300388793113364709799321765759268567418651) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 56 = 27 +
      29 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (184 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_184 :
    recurrence2Scalar0Main.coeff 184 =
      (((2641193233714419178067940111667302341148905990352091552396 * 10 ^ 70 +
        5747815016711727812988460423759953652738057299943259305450973132637579) * 10 ^ 70 +
        3152124554896352290552973763427823489947567701137042858732949713748414) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 57 = 27 +
      30 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (185 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_185 :
    recurrence2Scalar0Main.coeff 185 =
      (((2663859017451319997522953938453363818914473544430614108876 * 10 ^ 70 +
        8792829567019254598403684741317566589425185135233750753174380697495685) * 10 ^ 70 +
        2128063679149984456723586188501930735224914494616572013832386666261505) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 58 = 27 +
      31 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (186 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_186 :
    recurrence2Scalar0Main.coeff 186 =
      -(((31041132306282617925750941813994889269848742173492734586202 * 10 ^ 70 +
        6853828326381268050078968952276494123459326517364936606277746133822051) * 10 ^ 70 +
        1257935217868528113535611515230396557959182309944944888732174026584115) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 59 = 27 +
      32 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (187 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_187 :
    recurrence2Scalar0Main.coeff 187 =
      (((99917177950028534143660442325423378536441738793802589652516 * 10 ^ 70 +
        9621077905624137899620137026066913927147826550293067555980625273091365) * 10 ^ 70 +
        3401711865105219668394078075633191295635908010656710037556953323921092) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 60 = 27 +
      33 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (188 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_188 :
    recurrence2Scalar0Main.coeff 188 =
      -(((152794160252542267032571646025116035549135145926004393055175 * 10 ^ 70 +
        7594253722389174734420994146908140464695112592075353464004109933501532) * 10 ^ 70 +
        9392429736690147763280640897516524222732393640699142173637926326685696) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 61 = 27 +
      34 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (189 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_189 :
    recurrence2Scalar0Main.coeff 189 =
      -(((150448495943284316295839387464264791369112993534740301155754 * 10 ^ 70 +
        7985741001702792382601802101766365310986423979646727692649767022569783) * 10 ^ 70 +
        9714297736305842450905921230270533127581786786594460124397731428316190) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 62 = 27 +
      35 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (190 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_190 :
    recurrence2Scalar0Main.coeff 190 =
      (((1703743167712887811501546758086080559353795282957180788159182 * 10 ^ 70 +
        0160233911715642624583379919836749633375235594958314304651484263722169) * 10 ^ 70 +
        3609376075695987589822731430214429259019912660984752492789451109498718) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 63 = 27 +
      36 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (191 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_191 :
    recurrence2Scalar0Main.coeff 191 =
      -(((5548085880316504179897276305730069119956546768853737738241036 * 10 ^ 70 +
        0977395126384376693387948176721297819273617211535954464003759291418536) * 10 ^ 70 +
        1522246390353240727346891250663017967418528750468372295217308439221748) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 64 = 27 +
      37 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (192 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_192 :
    recurrence2Scalar0Main.coeff 192 =
      (((9560459870034323285242604932275561095830414893657628456656102 * 10 ^ 70 +
        4761581246193050360533354652082524013332169164730996610361063051032235) * 10 ^ 70 +
        0974509136883626576879000518737012247530674044666189809978607740660313) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 65 = 27 +
      38 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (193 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_193 :
    recurrence2Scalar0Main.coeff 193 =
      (((1278709975547349164516181566116822000310088627049690011115619 * 10 ^ 70 +
        0762179600855055802394580215542101448117842861431592030808561842736533) * 10 ^ 70 +
        6509183558074379361618555303088775464926836965687265586028771395897000) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 66 = 27 +
      39 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (194 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_194 :
    recurrence2Scalar0Main.coeff 194 =
      -(((70163603456582543928929191167213511672628098400537786134253402 * 10 ^ 70 +
        9828169056818477860378417864751272070268117065426375886585681758772237) * 10 ^ 70 +
        1674301120775667733103162986255562568567428311380013821978597816506231) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 67 = 27 +
      40 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_194_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (195 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_195 :
    recurrence2Scalar0Main.coeff 195 =
      (((264795419559115171876443780699862189338149976486147313284495972 * 10 ^ 70 +
        4178241022389147289154233627710254134906931459149350838592441239535607) * 10 ^ 70 +
        6521470963498048547472404899123177776844374658041124810535199131161659) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 68 = 27 +
      41 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_195_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (196 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_196 :
    recurrence2Scalar0Main.coeff 196 =
      -(((570358541660891143736765378833160056791470122646103939413633491 * 10 ^ 70 +
        1646209704806772239920199443885877143099250514155195381648686019391266) * 10 ^ 70 +
        1709067140744600760609333099166620456438606110200683764282982759774679) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 69 = 27 +
      42 by norm_num, Finset.sum_range_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_196_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
