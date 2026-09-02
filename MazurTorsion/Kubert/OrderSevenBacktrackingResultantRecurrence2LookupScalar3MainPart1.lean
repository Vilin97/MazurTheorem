/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB3
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3MainPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
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

private theorem recurrence2Scalar3Main_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (234 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_234 :
    recurrence2Scalar3Main.coeff 234 =
      ((((54 * 10 ^ 70 +
        1164966539149735546601603995011803981478227082542677347830828747361599) * 10 ^ 70 +
        4533003774513500804225582571109020499058927465771033531748157230206978) * 10 ^ 70 +
        8309670665513616030647331048650156337520537484887094998553060402756873) : ℚ) := by
  unfold recurrence2Scalar3Main
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
    rw [show 106 = 14 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (235 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_235 :
    recurrence2Scalar3Main.coeff 235 =
      -((((53 * 10 ^ 70 +
        1969191466284094870478023684254913631173741737467820995429767027343483) * 10 ^ 70 +
        1218122681382127646978080065491956409694078096056930063544533275938331) * 10 ^ 70 +
        6393342574763886391546157136310364580703159301576456100990394982918913) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 2 +
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
    rw [show 106 = 13 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (236 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_236 :
    recurrence2Scalar3Main.coeff 236 =
      ((((49 * 10 ^ 70 +
        0325993046814150879211896921145184616428839776249239008271796694207782) * 10 ^ 70 +
        1965881207993293892524584368478561298910035308257917759482802181379446) * 10 ^ 70 +
        1280164960302583063597557478484143891811332873273022262088162616632743) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 3 +
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
    rw [show 106 = 12 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (237 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_237 :
    recurrence2Scalar3Main.coeff 237 =
      -((((41 * 10 ^ 70 +
        9241833972500035685300498072637660697518726201239487192613402429733526) * 10 ^ 70 +
        0684138708925954882284659555523316930376441596628744050987559775680437) * 10 ^ 70 +
        0139595360703571643229089276741434918007087914340745260180605721783037) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 4 +
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
    rw [show 106 = 11 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (238 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_238 :
    recurrence2Scalar3Main.coeff 238 =
      ((((32 * 10 ^ 70 +
        5599735749146773816589788519031369148816740992367551310184559040068328) * 10 ^ 70 +
        3349721231351732960519339416564967483290538217659147065531020252940817) * 10 ^ 70 +
        2154873644004389200321253293244953147445872944567959834113054412794689) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 5 +
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
    rw [show 106 = 10 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (239 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_239 :
    recurrence2Scalar3Main.coeff 239 =
      -((((21 * 10 ^ 70 +
        9077833109109958593601273324530340261344461866985404003424780559045027) * 10 ^ 70 +
        0386272771792919256573759553286403259674501235448888252333110761809920) * 10 ^ 70 +
        2140147096840530750297769208509912071599396588031975883887075071443201) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 6 +
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
    rw [show 106 = 9 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (240 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_240 :
    recurrence2Scalar3Main.coeff 240 =
      ((((11 * 10 ^ 70 +
        0565272066470752341444156902781242513412456584227042123805499174417563) * 10 ^ 70 +
        8216028353614639173181493168923600848389345521920900178787146381725373) * 10 ^ 70 +
        3646975155910606907302034507478771952083202049534176712440030242203213) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 7 +
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
    rw [show 106 = 8 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (241 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_241 :
    recurrence2Scalar3Main.coeff 241 =
      -((((1 * 10 ^ 70 +
        0422714831767977058836269101166476672260726624281147512617436653791546) * 10 ^ 70 +
        7563109272459768321289144421344824705208776606543025594703908624792397) * 10 ^ 70 +
        1555640653633201627389989952894909884026735249689593294315534457007328) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 8 +
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
    rw [show 106 = 7 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (242 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_242 :
    recurrence2Scalar3Main.coeff 242 =
      -((((7 * 10 ^ 70 +
        3044039617812544741010347461572109869309812128972759376273739232052354) * 10 ^ 70 +
        7852010539231146451145132235321721900207748532771266291912456717158289) * 10 ^ 70 +
        5103394052911185476968053483565540982964899767314193216415694264012143) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 9 +
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
    rw [show 106 = 6 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (243 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_243 :
    recurrence2Scalar3Main.coeff 243 =
      ((((13 * 10 ^ 70 +
        4603282072597760470304862592583831226332453458486602967715214590277275) * 10 ^ 70 +
        3491182516529960114700230518025949297173994365085137220400435052424138) * 10 ^ 70 +
        5389551302100933492553123106529242222366075792117597695309950183774526) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 10 +
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
    rw [show 106 = 5 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (244 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_244 :
    recurrence2Scalar3Main.coeff 244 =
      -((((17 * 10 ^ 70 +
        2458141726465286478280368245004086425013321857355148835991391193808325) * 10 ^ 70 +
        0022031779032100926696422744917953644430196729632947831142383794864107) * 10 ^ 70 +
        8768281103766667799416903525038716881230637372439552981874201988097985) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 11 +
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
    rw [show 106 = 4 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_244_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (245 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_245 :
    recurrence2Scalar3Main.coeff 245 =
      ((((18 * 10 ^ 70 +
        7962897526260645944531419406109451753531543671816705308867046860451422) * 10 ^ 70 +
        9504374103066270174687539960111501154780897749590184315814147510996606) * 10 ^ 70 +
        1313719659578324729293963285106709413311368712417669465085510309179318) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 12 +
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
    rw [show 106 = 3 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_245_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (246 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_246 :
    recurrence2Scalar3Main.coeff 246 =
      -((((18 * 10 ^ 70 +
        4849488473483090022184904196211074259382804381394804475559748840072349) * 10 ^ 70 +
        8354564263898338265003672732030428222868488380586736089594360214493141) * 10 ^ 70 +
        2763337791108759320474025642349292820386985650384873312960150135525651) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 13 +
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
    rw [show 106 = 2 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (247 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_247 :
    recurrence2Scalar3Main.coeff 247 =
      ((((16 * 10 ^ 70 +
        8200577179998861779256263826708946227100218158739156906099401208262715) * 10 ^ 70 +
        2962621968472252454224708129808422636383916835987987096748516720235774) * 10 ^ 70 +
        7217942974870777151531119792067889192362376323006604274593231058057294) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 14 +
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
    rw [show 106 = 1 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (248 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_248 :
    recurrence2Scalar3Main.coeff 248 =
      -((((14 * 10 ^ 70 +
        3416319013111026302774789311400108922143226551281696993518125799437850) * 10 ^ 70 +
        5743036358555700549235625658305985229846398920311085785007045379858863) * 10 ^ 70 +
        4627558796350444379574167047002403997156642361205375557120782157823697) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 15 +
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
  rw [recurrence2Scalar3Main_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (249 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_249 :
    recurrence2Scalar3Main.coeff 249 =
      ((((11 * 10 ^ 70 +
        5372042458261108261176597179552285248649843040030268074561351334428924) * 10 ^ 70 +
        1811023116298507826984311121725549532007165378375575617233864215550054) * 10 ^ 70 +
        5529052621011179450831523518327747665564809481416540008443809221807282) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 16 +
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
    rw [show 138 = 31 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (250 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_250 :
    recurrence2Scalar3Main.coeff 250 =
      -((((8 * 10 ^ 70 +
        7878626948446116725615264809023843481021680467613525579659961355094156) * 10 ^ 70 +
        1297935420965957570337627364602125005592743632424858211645825365464313) * 10 ^ 70 +
        2681688156202003361929836703612967306572461194680761544107182264824568) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 17 +
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
    rw [show 138 = 30 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (251 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_251 :
    recurrence2Scalar3Main.coeff 251 =
      ((((6 * 10 ^ 70 +
        3466211519919283742016542639496263658270874410446801954646767812152370) * 10 ^ 70 +
        9010795609716983998670800172025014927768475124686671099922232682697389) * 10 ^ 70 +
        9970342291889072064585184005371539641523033708423313021909544592533157) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 18 +
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
    rw [show 138 = 29 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (252 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_252 :
    recurrence2Scalar3Main.coeff 252 =
      -((((4 * 10 ^ 70 +
        3439372205338068539200612430446795221643761850476307789193119095512909) * 10 ^ 70 +
        1042874153925452623047526434815266179900937974448093271352272066259292) * 10 ^ 70 +
        2356378494501301478812845704117195078973724617641878817973550640402182) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 19 +
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
    rw [show 138 = 28 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (253 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_253 :
    recurrence2Scalar3Main.coeff 253 =
      ((((2 * 10 ^ 70 +
        8111238603587450181889019480788286328038984343198913101159874730001093) * 10 ^ 70 +
        9394087309445255582271091151018780560174015381040211123917237939103358) * 10 ^ 70 +
        6866850908722520075574385703551674414875449991976242770082446927236446) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 20 +
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
    rw [show 138 = 27 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (254 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_254 :
    recurrence2Scalar3Main.coeff 254 =
      -((((1 * 10 ^ 70 +
        7116220194358226389976833451253753990238861645718846152073941084896228) * 10 ^ 70 +
        0246995787415005647618912264840204623454783070936566269371221746072317) * 10 ^ 70 +
        3287607334911823726186058454914280441283957903871419943733341141807270) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 21 +
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
    rw [show 138 = 26 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (255 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_255 :
    recurrence2Scalar3Main.coeff 255 =
      (((9718067991111960953348137151329105630722371758370202090434445467022144 * 10 ^ 70 +
        3463592887726662760331988597737083527059892110798604432069355000037231) * 10 ^ 70 +
        8028759360884182519948964395345605417937549150711124161216917859432248) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 22 +
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
    rw [show 138 = 25 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (256 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_256 :
    recurrence2Scalar3Main.coeff 256 =
      -(((5059808887702969900446270908578813708943124273536035897996481086488521 * 10 ^ 70 +
        6631915757695932977506019407030089380213150953495733479558046788544732) * 10 ^ 70 +
        7199640670515527133427714850734173709384053294083846785869301492468097) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 23 +
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
    rw [show 138 = 24 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (257 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_257 :
    recurrence2Scalar3Main.coeff 257 =
      (((2333172285203134334283280757107262423285433016408168270435161397113390 * 10 ^ 70 +
        4571716473517796023887611320911153030884736312020315250944413093125734) * 10 ^ 70 +
        0187684014388509763642134349148661289208959672465378590880771453767959) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 24 +
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
    rw [show 138 = 23 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (258 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_258 :
    recurrence2Scalar3Main.coeff 258 =
      -(((869614256845847575032870811483479012746796623795332046038791350923342 * 10 ^ 70 +
        1346577657010523898529409711078587777556080617149782556165258947405118) * 10 ^ 70 +
        3049727480199947685772309170934091738630082256697818154807816995920051) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 25 +
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
    rw [show 138 = 22 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (259 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_259 :
    recurrence2Scalar3Main.coeff 259 =
      (((169601654000218184508545972348635947471022796923544036245007006467696 * 10 ^ 70 +
        5756258007687282829522097111491288985585558861916640045388866625719626) * 10 ^ 70 +
        5720073629690070256417184272551243967178754138068619891208484471943901) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 26 +
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
    rw [show 138 = 21 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (260 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_260 :
    recurrence2Scalar3Main.coeff 260 =
      (((108094588256814028496095143726971729266740869915708281890767837092299 * 10 ^ 70 +
        6517135522680745776841212213647754250527536464008856101191549089481914) * 10 ^ 70 +
        1460142284427872399172997594894615401563008576617776113721653464208567) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 27 +
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
    rw [show 138 = 20 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (261 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_261 :
    recurrence2Scalar3Main.coeff 261 =
      -(((177058128958901306463843645921366577124019307955409451262879458454941 * 10 ^ 70 +
        6146251650798696218695138479704118882043816086470764277136055769416162) * 10 ^ 70 +
        4011659201488758832288941435299750461253047253956324374719919067413068) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 28 +
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
    rw [show 138 = 19 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (262 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_262 :
    recurrence2Scalar3Main.coeff 262 =
      (((159025798667625436384909707800380707863687076958882677133245768470281 * 10 ^ 70 +
        7127064775113590253436559278730126420631240767529541877893765368980328) * 10 ^ 70 +
        2168363173579478123327480809426857573082743907476717602373445282154027) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 29 +
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
    rw [show 138 = 18 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (263 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_263 :
    recurrence2Scalar3Main.coeff 263 =
      -(((116001351076561385799993989282068827068713763503957896021667907527996 * 10 ^ 70 +
        4376389082283199608368269962402571274254494239751113224566315554541261) * 10 ^ 70 +
        1532021816277858148110744216573871803060044974040786100437744939912592) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 30 +
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
    rw [show 138 = 17 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (264 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_264 :
    recurrence2Scalar3Main.coeff 264 =
      (((74885717944153420102075996652614211950781432915971868274292967597670 * 10 ^ 70 +
        4734055163953886718085429311699951609779597902109689643895336950290560) * 10 ^ 70 +
        9451924072267550267814705857115231338725874146674662793730660179012393) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 31 +
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
    rw [show 138 = 16 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (265 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_265 :
    recurrence2Scalar3Main.coeff 265 =
      -(((44196160570995650727849841228368019153178809388639681144850810336492 * 10 ^ 70 +
        0197177757332882180736837415812686392466864828118381779104999929441353) * 10 ^ 70 +
        0278195316739743515616242651685760948911147973788850896949201079357559) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 32 +
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
    rw [show 138 = 15 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (266 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_266 :
    recurrence2Scalar3Main.coeff 266 =
      (((24204886171605188760400319603058213332391845295593657230093164178688 * 10 ^ 70 +
        8273760950345393413637761134699141509776286717242044804820327310757743) * 10 ^ 70 +
        7182310523263326553847281143494458611355449042927551664540081023001269) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 33 +
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
    rw [show 138 = 14 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (267 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_267 :
    recurrence2Scalar3Main.coeff 267 =
      -(((12388590478314646731178598357776351291151386610318799138270734296330 * 10 ^ 70 +
        5894792933542848533014004197804951754727567346840913225214806949847102) * 10 ^ 70 +
        6925877985185385715319082348872040972126684996530498707689091011794891) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 34 +
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
    rw [show 138 = 13 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (268 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_268 :
    recurrence2Scalar3Main.coeff 268 =
      (((5940813839287637451132957439000820360257762292412789904764358985941 * 10 ^ 70 +
        6662029040138079173882114368128426206071894159155554382801902244967981) * 10 ^ 70 +
        3054810114963913675678296932679317319520598498874591141100259887397996) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 35 +
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
    rw [show 138 = 12 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (269 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_269 :
    recurrence2Scalar3Main.coeff 269 =
      -(((2666802376120613596873895650347892422781737409121881727912289908587 * 10 ^ 70 +
        1068726651267346630853372592016286505250598271461556533045021346024386) * 10 ^ 70 +
        2699135688904567922660448070117544037331177928754253744978358251390715) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 36 +
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
    rw [show 138 = 11 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (270 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_270 :
    recurrence2Scalar3Main.coeff 270 =
      (((1115604904178620488386502206554505361127992811386663227594307313646 * 10 ^ 70 +
        6024730639784404970383154248689324809093474188271266963252597004008526) * 10 ^ 70 +
        6868979970757422635192548483354315581282764427272977655541632941366762) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 37 +
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
    rw [show 138 = 10 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (271 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_271 :
    recurrence2Scalar3Main.coeff 271 =
      -(((430744353780569369423749442556651885611025804187034051063993915170 * 10 ^ 70 +
        7256435280591872366820314889056323224304457244795228707735558419269458) * 10 ^ 70 +
        2077297749367410615077115624926052148114886832310114238280891519194934) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 38 +
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
    rw [show 138 = 9 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (272 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_272 :
    recurrence2Scalar3Main.coeff 272 =
      (((150577772455983169660986560081273063523761366906847636382822351176 * 10 ^ 70 +
        9257022589507058641859468975494347940668220177940967411992912782043527) * 10 ^ 70 +
        1221625708530504173769867476565485310247357020913479613536573194492610) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 39 +
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
    rw [show 138 = 8 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (273 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_273 :
    recurrence2Scalar3Main.coeff 273 =
      -(((45684681301099346118948812473545993719735960838456283676650674406 * 10 ^ 70 +
        6319551781627228234914363045397015088121687517820033922275342267500876) * 10 ^ 70 +
        9613702487403242956355457926679141267388800049184162330556370784894653) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 40 +
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
    rw [show 138 = 7 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (274 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_274 :
    recurrence2Scalar3Main.coeff 274 =
      (((10657921549849786559920887717179808954585521561659664337284628018 * 10 ^ 70 +
        7024224976219736016377321039068975036437060604134416263398072451134238) * 10 ^ 70 +
        4478389355524569244015271657588715502417853611782852003424828853148398) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 41 +
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
    rw [show 138 = 6 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (275 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_275 :
    recurrence2Scalar3Main.coeff 275 =
      -(((852003982832320739243649349730457034806448822045747583206151520 * 10 ^ 70 +
        8507202233445109118710633886834117530509625738952052976076065419147539) * 10 ^ 70 +
        7872588602801473004049205334200914618612787718009133058309498960374550) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 42 +
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
    rw [show 138 = 5 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (276 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_276 :
    recurrence2Scalar3Main.coeff 276 =
      -(((998027627971638451677637382258230442174017424570958151695818868 * 10 ^ 70 +
        9836976544375509676727806243698373162005643935546800909361614699960254) * 10 ^ 70 +
        4032622102134829549638671825443141395242941612334086848360284531381062) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 43 +
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
    rw [show 138 = 4 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (277 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_277 :
    recurrence2Scalar3Main.coeff 277 =
      (((857080073605518771727619224734946190368433948973176958263812819 * 10 ^ 70 +
        3955898200771636831245282711418259424203876535415564618566200766153155) * 10 ^ 70 +
        6636022580414889157454610272814580930449048542115978155406355496478145) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 44 +
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
    rw [show 138 = 3 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (278 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_278 :
    recurrence2Scalar3Main.coeff 278 =
      -(((473745946226207210482866774644307539250879170100151411551751121 * 10 ^ 70 +
        9434260628304484040657987010741365807565852685929394885682407993400241) * 10 ^ 70 +
        5226387952569109389318822805574989293333431927963597310503081318348231) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 45 +
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
    rw [show 138 = 2 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (279 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_279 :
    recurrence2Scalar3Main.coeff 279 =
      (((216406296623636157932143849344867834367903069763641575370551390 * 10 ^ 70 +
        6968455973720271838121987930878190279131969400979680003537840091571956) * 10 ^ 70 +
        3873500281133425050895749228827686596641672387989054522696989897461185) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 46 +
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
    rw [show 138 = 1 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (280 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_280 :
    recurrence2Scalar3Main.coeff 280 =
      -(((87134146387375380737817877704927565949508282155711619704251503 * 10 ^ 70 +
        9576081955857996190414335156830563465981378063803977854334857663735350) * 10 ^ 70 +
        2442528698706266955873114718954594765266022944035846814606410817738959) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 47 +
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
  rw [recurrence2Scalar3Main_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (281 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_281 :
    recurrence2Scalar3Main.coeff 281 =
      (((31659925596768068227475919541312441284068607667344288878776061 * 10 ^ 70 +
        3080910486260768986874519623403782766322795562636081869191765067902086) * 10 ^ 70 +
        7099402027998192470123772056574836898590074487177911687743113420443190) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 48 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 31 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (282 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_282 :
    recurrence2Scalar3Main.coeff 282 =
      -(((10457957314219917122308376583943194350575855497736422582420039 * 10 ^ 70 +
        6781024033515678786640159643449116496210080427140252638065910249345866) * 10 ^ 70 +
        5406372383120528688013912631903569628217325974968966648527676114408773) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 49 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 30 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (283 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_283 :
    recurrence2Scalar3Main.coeff 283 =
      (((3131603257604752342637216371090061146143543734309247741628639 * 10 ^ 70 +
        4131860726224602470881789240594773661872567072179617333874321789477157) * 10 ^ 70 +
        8666935042480809701003923696225318154959486216222823909820943894844089) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 50 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 29 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (284 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_284 :
    recurrence2Scalar3Main.coeff 284 =
      -(((838040872240128151009836147372862475923962424772882708288753 * 10 ^ 70 +
        5343462762308449416492762383961032744632007462985339025645199378645674) * 10 ^ 70 +
        2290319619438213433889759443027804273584389557287743782883596024158333) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 51 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 28 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (285 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_285 :
    recurrence2Scalar3Main.coeff 285 =
      (((193320957957718366722005325968499924551822056996891146872620 * 10 ^ 70 +
        8658060851725876264827973690991277024557724678661285743890415593259448) * 10 ^ 70 +
        6088561481769880857574143601073912075552256593197799155066957919258061) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 52 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 27 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (286 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_286 :
    recurrence2Scalar3Main.coeff 286 =
      -(((34706371975313315033060200118508994958059223569583751099177 * 10 ^ 70 +
        3609555797763573802495761659386718969868729142668206519689452530712736) * 10 ^ 70 +
        6424181472665946937376655782995720832480196797639306316441376093179372) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 53 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 26 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (287 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_287 :
    recurrence2Scalar3Main.coeff 287 =
      (((2788563521430606327605242724875503974826458614093511622155 * 10 ^ 70 +
        6647079257738332814102080014789087183420184849348023731467406963570588) * 10 ^ 70 +
        2175931689228439721457870117615203093188766171685910408532280464521097) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 54 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 25 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (288 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_288 :
    recurrence2Scalar3Main.coeff 288 =
      (((1264258603357699988763125030112956827915656282027186254269 * 10 ^ 70 +
        9439982845956095364560962385719316415305395057830964620425021323220522) * 10 ^ 70 +
        1320445313983433297294241674471691904995888105912350942319054437177524) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 55 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 24 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (289 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_289 :
    recurrence2Scalar3Main.coeff 289 =
      -(((855876510940271840694602809232969975151649961290712986474 * 10 ^ 70 +
        1558535698870416147110690896936158036711406971130988268989985279282200) * 10 ^ 70 +
        7826668479550626410489365876522078414210637535456144738490402579648596) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 56 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 23 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (290 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_290 :
    recurrence2Scalar3Main.coeff 290 =
      (((335864459369363613172529064044717096615350433080434779131 * 10 ^ 70 +
        6707072613193556777579863356628008854529324865990747585036860959749708) * 10 ^ 70 +
        5585760119737426491808933715571390054940846089824137352994985560335971) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 57 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 22 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (291 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_291 :
    recurrence2Scalar3Main.coeff 291 =
      -(((104505803404486941928940476658379951801981264145610556225 * 10 ^ 70 +
        5225575501096495722373539681234706913671561060954282585076389107209361) * 10 ^ 70 +
        6634609880303122860475839897696495837131987712185133839428908574134511) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 58 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 21 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (292 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_292 :
    recurrence2Scalar3Main.coeff 292 =
      (((27504518632942250159477524561650809729563088106479569671 * 10 ^ 70 +
        1633561353315742198409524489591837811380583365692056900296587690718159) * 10 ^ 70 +
        4051089551926101922145534107782389205909105444364093453866033200889752) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 59 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 20 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (293 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_293 :
    recurrence2Scalar3Main.coeff 293 =
      -(((6165839877988924623714510439889151863260012114614943058 * 10 ^ 70 +
        7896423863508955229749180015034250097110100848831901958819258330740722) * 10 ^ 70 +
        4347938881346287066877113096631393541426434936615778948863059458957183) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 60 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 19 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (294 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_294 :
    recurrence2Scalar3Main.coeff 294 =
      (((1134396968066132338164430902428948819719069428376288252 * 10 ^ 70 +
        0803910373078594978821443136465283946458565998977785147056703239988011) * 10 ^ 70 +
        9412311693941601569636915988520864239901407632127262488111866658335801) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 61 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 18 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (295 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_295 :
    recurrence2Scalar3Main.coeff 295 =
      -(((146985528207533720965719369205304415531001626264189916 * 10 ^ 70 +
        1882766788660655824086381957826997340455793464817651701942113839088069) * 10 ^ 70 +
        1727979315099833223974910817575474008118731851320240933410507131516250) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 62 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 17 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (296 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_296 :
    recurrence2Scalar3Main.coeff 296 =
      (((1407181411269679251801493356222135590894491518449083 * 10 ^ 70 +
        6112145700353507320984135983524100684050318283410483794481576766193633) * 10 ^ 70 +
        8996091083385617862807568993729605131077754870259285250847019746213885) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 63 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 16 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (297 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_297 :
    recurrence2Scalar3Main.coeff 297 =
      (((6973938830855177896356229713803418336345656284486569 * 10 ^ 70 +
        8234191758703816994113576618367908033710933423012842019187428538413536) * 10 ^ 70 +
        3664616844196358035237058173653591173683172468294375201071340255673263) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 64 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 15 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (298 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_298 :
    recurrence2Scalar3Main.coeff 298 =
      -(((2890564902926312474599065424665469809593653305314218 * 10 ^ 70 +
        3666062476370275059216940433904652464760736994042843791421096587133993) * 10 ^ 70 +
        5890937733882717658542821054256334726927334979606411641459488702946695) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 65 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 14 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (299 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_299 :
    recurrence2Scalar3Main.coeff 299 =
      (((814866825633855485466514132158075398481972194775665 * 10 ^ 70 +
        2488253208765427507932029457500927697469711758493867114415851983555574) * 10 ^ 70 +
        0283695272251487468522480078773504303994464757808198988184914997601063) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 66 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 13 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (300 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_300 :
    recurrence2Scalar3Main.coeff 300 =
      -(((185164712616839617507480539195290117464623871453900 * 10 ^ 70 +
        2732196576794134185335859228184771470867015414316518620276899792246851) * 10 ^ 70 +
        2194007969441810742188974992851699487600392221777313777371513609259463) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 67 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 12 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (301 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_301 :
    recurrence2Scalar3Main.coeff 301 =
      (((35118775184580372917778748151365579115304863699958 * 10 ^ 70 +
        1474497676683496897745337417823739091180789236206430448040723721227350) * 10 ^ 70 +
        4725723241058785128141952583748836035495253659618563230591608187644576) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 68 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 11 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (302 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_302 :
    recurrence2Scalar3Main.coeff 302 =
      -(((5456513335144965230698828377541190369761229737079 * 10 ^ 70 +
        3510597207070737748310999014706896219267228650986608709507658569479465) * 10 ^ 70 +
        6220421363541936947357981422277325686251953641068542502369322538983372) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 69 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 10 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (303 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_303 :
    recurrence2Scalar3Main.coeff 303 =
      (((624612380390467090721255784475503926346902674945 * 10 ^ 70 +
        5487398932846636333633068054821804581632052813115559130750234874730999) * 10 ^ 70 +
        9224654286944963294164426133843888642308753522110209025029962435548368) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 70 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 9 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (304 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_304 :
    recurrence2Scalar3Main.coeff 304 =
      -(((25241065933619520324423178487037704115135551924 * 10 ^ 70 +
        3864182195915755828096809065944054945493141964257873060859926118783004) * 10 ^ 70 +
        8618061370627163782185947208083924492532322258220238892170440781306778) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 71 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 8 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (305 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_305 :
    recurrence2Scalar3Main.coeff 305 =
      -(((11454098740583137159485003097919355376941692322 * 10 ^ 70 +
        8814344972379521111500353040675822428024373912460860427872361341705993) * 10 ^ 70 +
        5987035773980739145005836324528437673405054118765773570838706711780077) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 72 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 7 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (306 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_306 :
    recurrence2Scalar3Main.coeff 306 =
      (((4295022703738666900171813900285955269298540702 * 10 ^ 70 +
        3093343551528902520896906074000210794744623091107265039797900564751772) * 10 ^ 70 +
        0993983027379306499620378600536672018119096763730570942466082786465278) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 73 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 6 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (307 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_307 :
    recurrence2Scalar3Main.coeff 307 =
      -(((973731699586103178823314665885103122109225704 * 10 ^ 70 +
        2169244579754991377040233406564496755813270552598072799013459053065769) * 10 ^ 70 +
        6986701026058037286058426445595668977308819466775759513490486467042465) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 74 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 5 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (308 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_308 :
    recurrence2Scalar3Main.coeff 308 =
      (((172056346947569299453566413159372365991018544 * 10 ^ 70 +
        7866940503789689407229756485412628563068872899889641951914070644645883) * 10 ^ 70 +
        5214156570685288396636093745015777746109220484742500930699871684469960) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 75 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 4 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (309 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_309 :
    recurrence2Scalar3Main.coeff 309 =
      -(((24902817603610363796931634553893598301259877 * 10 ^ 70 +
        2817454621768606497044424693581789378606858134675424955390882020511936) * 10 ^ 70 +
        5257576291362144528555024360553951549332091805402437298251793335574855) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 76 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 3 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (310 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_310 :
    recurrence2Scalar3Main.coeff 310 =
      (((2916092377889816514637807867222312171865635 * 10 ^ 70 +
        8848267418265666330417084795584352892166821460100340750502437866217328) * 10 ^ 70 +
        4090968720382749554418403441926774671954272615094916773113276564444777) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 77 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 2 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (311 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_311 :
    recurrence2Scalar3Main.coeff 311 =
      -(((251240920670505842193736978003382228179135 * 10 ^ 70 +
        4834564055766587333256890080158178026365683081474928734563903957162625) * 10 ^ 70 +
        6229319884475547742829168111111456499650152833294256568078176069750632) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 78 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 1 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (312 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_312 :
    recurrence2Scalar3Main.coeff 312 =
      (((8805210615536016779577803460685874876250 * 10 ^ 70 +
        5495666769632147644529898159810774230923686595220559530465947562975732) * 10 ^ 70 +
        9950637490256630241733007601069393283737100347916271948716927108623607) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 79 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (313 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_313 :
    recurrence2Scalar3Main.coeff 313 =
      (((1999716824322005212568913876906387234039 * 10 ^ 70 +
        5558448069549932007445386414314195929365214170811480649995061568581658) * 10 ^ 70 +
        6523050289389368421537942208972556192672985035147834930540374436954251) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 80 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 31 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (314 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_314 :
    recurrence2Scalar3Main.coeff 314 =
      -(((555095645760425938459262589478149762826 * 10 ^ 70 +
        8384936004056899572451452320163811092771546694745077268079183063401307) * 10 ^ 70 +
        9019328776270783082523544358778779895490139798520284725198993962298275) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 81 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 30 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (315 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_315 :
    recurrence2Scalar3Main.coeff 315 =
      (((86519474184458681390643059364195080291 * 10 ^ 70 +
        5653536968226898167114375663534857232849579295871669549841997233210428) * 10 ^ 70 +
        8272532398602938990788869849836394646901892271425528721830414904338195) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 82 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 29 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (316 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_316 :
    recurrence2Scalar3Main.coeff 316 =
      -(((10055648947245849796371390117606388301 * 10 ^ 70 +
        3728050873212933008365272960651850497269889681638017209721621886184812) * 10 ^ 70 +
        4750203202929969752366189821209182967544333090776220182420767469691198) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 83 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 28 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (317 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_317 :
    recurrence2Scalar3Main.coeff 317 =
      (((902275921074042747823421164506234482 * 10 ^ 70 +
        3167839297346657661804552323193470297988283862733566107354784369805736) * 10 ^ 70 +
        1955740923095030505285321865252982221201408176875152594035812244972012) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 84 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 27 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (318 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_318 :
    recurrence2Scalar3Main.coeff 318 =
      -(((58026627001904880628133921911455555 * 10 ^ 70 +
        2398294457887922400252785885845991982916762901832223278589051499068745) * 10 ^ 70 +
        7821734524092012910215410092217394554090565258552552509853977962825738) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 85 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 26 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (319 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_319 :
    recurrence2Scalar3Main.coeff 319 =
      (((1603211975525481558951495622676910 * 10 ^ 70 +
        2874577334856009216376089223553589350877692363071189169958573388692779) * 10 ^ 70 +
        6002143572459794045199924058987453349083386306454321248348011808110531) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 86 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 25 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (320 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_320 :
    recurrence2Scalar3Main.coeff 320 =
      (((200545866310141171200596656116732 * 10 ^ 70 +
        0997725160844546802819940616937689483168706157956652957745756731213721) * 10 ^ 70 +
        7659219080982788907407163066331377166862398497862405554844691499513254) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 87 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 24 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (321 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_321 :
    recurrence2Scalar3Main.coeff 321 =
      -(((39022776699149298175047610417549 * 10 ^ 70 +
        1943812669412329964631849347781204509100222776541266729518707486168290) * 10 ^ 70 +
        5953416401220893715342331269150441837079769864705391489642930890811537) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 88 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 23 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (322 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_322 :
    recurrence2Scalar3Main.coeff 322 =
      (((3916032774852756206789329257031 * 10 ^ 70 +
        6858724072062529282535495250813528302951741019815161823083662903970030) * 10 ^ 70 +
        2815147988139901639820209800168664404783450348548324260543137609855839) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 89 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 22 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (323 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_323 :
    recurrence2Scalar3Main.coeff 323 =
      -(((271844801033187930652992634781 * 10 ^ 70 +
        3950522963099804609670688707449089775453756993403652444254236241805848) * 10 ^ 70 +
        2549423539589936615813955666498960735419700766088774440458710640618993) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 90 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 21 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (324 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_324 :
    recurrence2Scalar3Main.coeff 324 =
      (((12646462646109643096007031200 * 10 ^ 70 +
        7307446862446507720156460278802081477623569767838102119177907227957437) * 10 ^ 70 +
        4141618120307313093997294397746821077868294386565658833131000614432642) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 91 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 20 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (325 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_325 :
    recurrence2Scalar3Main.coeff 325 =
      -(((227458577910624116380496957 * 10 ^ 70 +
        1151970163145198983793850570536833249143427452966269533995404931825355) * 10 ^ 70 +
        1229378888844883902184923910265539683253170998501193549423683613211555) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 92 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 19 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (326 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_326 :
    recurrence2Scalar3Main.coeff 326 =
      -(((22060307458056858573776680 * 10 ^ 70 +
        2742965028463542144841548005301936644183958638675093197560016143793888) * 10 ^ 70 +
        2838197821595619528292459140867269610683406186115749616542545096383655) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 93 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 18 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (327 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_327 :
    recurrence2Scalar3Main.coeff 327 =
      (((2605396914418006695186825 * 10 ^ 70 +
        2920705391471629368139637051004551401289609435451508866164305720542410) * 10 ^ 70 +
        0715440638817614288199767801537715381115145824680455426684322995311714) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 94 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 17 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (328 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_328 :
    recurrence2Scalar3Main.coeff 328 =
      -(((151188317885324379519969 * 10 ^ 70 +
        6137041747042726990565905904050583301062105977729392847240960397089195) * 10 ^ 70 +
        4260073094190612823630773801274348717243069634632255232867699964020362) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 95 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 16 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (329 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_329 :
    recurrence2Scalar3Main.coeff 329 =
      (((5278665370833421395663 * 10 ^ 70 +
        8740164096084032084609048177988584398037052912828969258663084480661186) * 10 ^ 70 +
        3429950564388058390569778212148651263519248536793867509382333871912882) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 96 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 15 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (330 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_330 :
    recurrence2Scalar3Main.coeff 330 =
      -(((68859090651528469793 * 10 ^ 70 +
        7969849767752484875266904670357508985712394274389796581233874346168198) * 10 ^ 70 +
        3557215092802340704362431285996307787965860953103616794204063949674256) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 97 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 14 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (331 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_331 :
    recurrence2Scalar3Main.coeff 331 =
      -(((3930991366689307628 * 10 ^ 70 +
        5451876669091095982459652135156222482584779415492139542926750459280186) * 10 ^ 70 +
        7194414855774975768607908381658737646764920152821140982762156634758550) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 98 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 13 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (332 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_332 :
    recurrence2Scalar3Main.coeff 332 =
      (((285777409730664993 * 10 ^ 70 +
        8122873705113988510470805247957583414912192807091648288043943717914729) * 10 ^ 70 +
        8409240661416927916920359388076119425528434593036600046013855344950691) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 99 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 12 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (333 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_333 :
    recurrence2Scalar3Main.coeff 333 =
      -(((8888908010870014 * 10 ^ 70 +
        8657312319113738654090137495028790614609560137916016839007856297620060) * 10 ^ 70 +
        7187604800183640848168775215694489139900160817396026332143660032299657) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 100 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 11 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (334 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_334 :
    recurrence2Scalar3Main.coeff 334 =
      (((116854177352502 * 10 ^ 70 +
        8158118774402293473149031204413937324668335896563227283763155461131593) * 10 ^ 70 +
        1005139917649009382451453912745013898968100961741118451213297792531985) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 101 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 10 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (335 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_335 :
    recurrence2Scalar3Main.coeff 335 =
      (((1750922446919 * 10 ^ 70 +
        0061743394608321238053718096383870263726278709486710843052622624770253) * 10 ^ 70 +
        2418534206576503394635202842838582610280462463319696767669134993652010) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 102 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 9 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (336 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_336 :
    recurrence2Scalar3Main.coeff 336 =
      -(((107959674446 * 10 ^ 70 +
        9225333703841156104156008173852431197445479329785181620083688724948828) * 10 ^ 70 +
        7241991646469612611057735268535162401629290687964743765388540351606169) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 103 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 8 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (337 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_337 :
    recurrence2Scalar3Main.coeff 337 =
      (((1884663971 * 10 ^ 70 +
        9785377622661776616866374433553561016638232067628478292554887693403514) * 10 ^ 70 +
        2873142734835629140300722737152186330014225187346491183904117943204044) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 104 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 7 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (338 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_338 :
    recurrence2Scalar3Main.coeff 338 =
      -(((4898361 * 10 ^ 70 +
        0788491664879469546306941899869022733809007133578294163561416656663439) * 10 ^ 70 +
        6589445899187454224112424006609015057994200169911602038862818053297566) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 105 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 6 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (339 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_339 :
    recurrence2Scalar3Main.coeff 339 =
      -(((343757 * 10 ^ 70 +
        1578135591434812802202397847425287784292572640122499591055103850275672) * 10 ^ 70 +
        8524538294965824231255298160404387906584153714364831816543285734205614) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 106 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 5 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (340 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_340 :
    recurrence2Scalar3Main.coeff 340 =
      (((5067 * 10 ^ 70 +
        1182101925265691289843067424444234438215564412063476466204674009736927) * 10 ^ 70 +
        0531396019312801258776535477456284750306159959135930191557755212676331) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 107 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 4 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (341 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_341 :
    recurrence2Scalar3Main.coeff 341 =
      -(((3 * 10 ^ 70 +
        9341431141227609449712504831374331606696822870537566591672964497591405) * 10 ^ 70 +
        3050710593208077166852922530600514941007490369756837094282863510571896) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 108 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 3 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (342 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_342 :
    recurrence2Scalar3Main.coeff 342 =
      -((4778237557511582460588221427924979934459483212060602151242774577903135 * 10 ^ 70 +
        7790776801434252816416388766412597380753176828114010987776614415886608) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 109 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 2 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (343 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_343 :
    recurrence2Scalar3Main.coeff 343 =
      ((29668455425142255874939421284696988459517192569218957371829325096431 * 10 ^ 70 +
        0237556265421164447122034376048015258799563390272425451045611911438761) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 110 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 1 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (344 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_344 :
    recurrence2Scalar3Main.coeff 344 =
      ((166916985704731742869475805256782866991875537515156814674666286923 * 10 ^ 70 +
        2246661718525594547739529318838955245821553642380500206910444918433226) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 111 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (345 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_345 :
    recurrence2Scalar3Main.coeff 345 =
      -((1981323786428731143894009634672114038067321074219440462835654806 * 10 ^ 70 +
        6792197942455042085233568355058259080275330069310665003394585567377682) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 112 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 31 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (346 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_346 :
    recurrence2Scalar3Main.coeff 346 =
      -((1199685497519141742457724410212726196435555271939008041676383 * 10 ^ 70 +
        8399383788552719951731628161819912127060079849214590921697183970828196) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 113 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 30 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (347 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_347 :
    recurrence2Scalar3Main.coeff 347 =
      ((61564055922767889602256591177876419690170722512946372262116 * 10 ^ 70 +
        5881460941978142326620289646749211743504198556864762391151391572971395) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 114 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 29 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (348 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_348 :
    recurrence2Scalar3Main.coeff 348 =
      -((80337872879041399892597217037475898175440256148485689887 * 10 ^ 70 +
        0354456540794459738598577328095293576348289907127034798950439391839428) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 115 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 28 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (349 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_349 :
    recurrence2Scalar3Main.coeff 349 =
      -((1011011743426859862429126295509566345437699374980465450 * 10 ^ 70 +
        2409001651423424244803796288511727761889834899535135460852938306426923) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 116 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 27 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (350 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_350 :
    recurrence2Scalar3Main.coeff 350 =
      ((2603554204576884480229214303844940043264812661411851 * 10 ^ 70 +
        6189572100654171654456003643214839673266937279896896641157383380648569) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 117 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 26 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (351 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_351 :
    recurrence2Scalar3Main.coeff 351 =
      ((8035689220888743100153990613346162932604383050985 * 10 ^ 70 +
        4805110598384613308725936789393159290760029459956787775057093375994292) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 118 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 25 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (352 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_352 :
    recurrence2Scalar3Main.coeff 352 =
      -((34046918081402955363175301061945386129686301004 * 10 ^ 70 +
        6364812102267598706349714533150843349949626919191361214140523664750928) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 119 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 24 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (353 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_353 :
    recurrence2Scalar3Main.coeff 353 =
      -((11786463213521943873862653440011711316133933 * 10 ^ 70 +
        2536134759651737908559657636892009818690126618936371341539265257489389) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 120 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 23 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (354 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_354 :
    recurrence2Scalar3Main.coeff 354 =
      ((201680414378786056348675651604448017461381 * 10 ^ 70 +
        3121056690450461993633853256624115705287357055785433785170584251929871) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 121 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 22 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (355 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_355 :
    recurrence2Scalar3Main.coeff 355 =
      -((217470769187859353523189956625444009385 * 10 ^ 70 +
        4197738609553228282079052834879395621384372141152853794279801676473217) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 122 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 21 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (356 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_356 :
    recurrence2Scalar3Main.coeff 356 =
      -((344862427486214934171974713618089552 * 10 ^ 70 +
        1274272735774837754129930434810746458339223078164623116296500425477203) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 123 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 20 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (357 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_357 :
    recurrence2Scalar3Main.coeff 357 =
      ((944911896614901108250324033028331 * 10 ^ 70 +
        8236022836045653825546664163565085772042618163878388296585279357981816) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 124 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 19 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (358 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_358 :
    recurrence2Scalar3Main.coeff 358 =
      -((666477497230144719845886657863 * 10 ^ 70 +
        7403741485820568547247400636095931058920220058905394976257614656364779) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 125 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 18 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (359 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_359 :
    recurrence2Scalar3Main.coeff 359 =
      -((103733007321054139442954873 * 10 ^ 70 +
        4155601737818951248997709831944983048669374711407727351143317055721170) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 126 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 17 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (360 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_360 :
    recurrence2Scalar3Main.coeff 360 =
      ((384427729432175074959455 * 10 ^ 70 +
        8380090236181902891753288779244483295801464696678825665641609762084431) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 127 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 16 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (361 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_361 :
    recurrence2Scalar3Main.coeff 361 =
      -((200206139422934497870 * 10 ^ 70 +
        2224804352240386667484014405995243854778179211209878417090722379307550) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 128 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 15 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (362 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_362 :
    recurrence2Scalar3Main.coeff 362 =
      ((39429648025563209 * 10 ^ 70 +
        8364646523311073969679119966465111196513387871055411802454818544558723) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 129 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 14 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (363 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_363 :
    recurrence2Scalar3Main.coeff 363 =
      -((997093484564 * 10 ^ 70 +
        7539641047792773013761370448257358671523047827457924987549430648819918) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 130 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 13 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (364 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_364 :
    recurrence2Scalar3Main.coeff 364 =
      -((587929229 * 10 ^ 70 +
        1435718098072894142810276353565002495858274168280100312655197017793198) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 131 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 12 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (365 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_365 :
    recurrence2Scalar3Main.coeff 365 =
      ((67490 * 10 ^ 70 +
        0410186325038640709911787723253957461484991914526096741768253599182360) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 132 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 11 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (366 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_366 :
    recurrence2Scalar3Main.coeff 366 =
      -((2 * 10 ^ 70 +
        4312380165204031645897398279054741405195371136309986581693564408074781) : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 133 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 10 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (367 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_367 :
    recurrence2Scalar3Main.coeff 367 =
      (271289961905851968575869918870047730514860505624753157701837189060 : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 134 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 9 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (368 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_368 :
    recurrence2Scalar3Main.coeff 368 =
      (739183213146172153150273377423511409092985393082071372576246 : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 135 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 8 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (369 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_369 :
    recurrence2Scalar3Main.coeff 369 =
      (-15126828093730794142694011544872504151918811435909631500 : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 136 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 7 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (370 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_370 :
    recurrence2Scalar3Main.coeff 370 =
      (41102881731970324944076495127153753583160341303338 : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 137 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 6 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (371 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_371 :
    recurrence2Scalar3Main.coeff 371 =
      (-17672599245882339987449193184198646207311255 : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 138 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 5 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (372 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_372 :
    recurrence2Scalar3Main.coeff 372 =
      (2009531077313996560625430689116346274 : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 139 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 4 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (373 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_373 :
    recurrence2Scalar3Main.coeff 373 =
      (16211427543469189257212460450 : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 140 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 3 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (374 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_374 :
    recurrence2Scalar3Main.coeff 374 =
      (-56341274563623035556 : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 141 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 2 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Main_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient3.coeff x * recurrence2QuotientConstant.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Main_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder3Coefficient3.coeff (143 + x) *
        recurrence2QuotientConstant.coeff (375 - (143 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B3_coeff_high (143 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Main_coeff_375 :
    recurrence2Scalar3Main.coeff 375 =
      (41146150404 : ℚ) := by
  unfold recurrence2Scalar3Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 142 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 1 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Main_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Main_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
