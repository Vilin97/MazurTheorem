/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0MainPart1Simp
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

private theorem recurrence2Scalar0Main_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (340 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_340 :
    recurrence2Scalar0Main.coeff 340 =
      -(((494219462828144338103 * 10 ^ 70 +
        4102098471322411246225289896608929383758375272298614605715274621689162) * 10 ^ 70 +
        3948921852712205251927880487877725745014830655814561508752840419852559) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 202 = 16 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (341 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_341 :
    recurrence2Scalar0Main.coeff 341 =
      (((23516903396949653512 * 10 ^ 70 +
        1742546516110390304967136170903102881007927892819012076363455812798776) * 10 ^ 70 +
        0045939865423566752530861195873941025203901601514661021668872626678100) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 202 = 15 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (342 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_342 :
    recurrence2Scalar0Main.coeff 342 =
      -(((550568247048044873 * 10 ^ 70 +
        6847831493317172176691086891946239376220396186364542335716319427349995) * 10 ^ 70 +
        1259187597441738280200218855424437431492712542643437085072587831850770) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 202 = 14 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (343 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_343 :
    recurrence2Scalar0Main.coeff 343 =
      -(((5732490478207690 * 10 ^ 70 +
        4424962135252817182430850885258721552920905260993744223586791221294751) * 10 ^ 70 +
        9668309568939981708776587269570762599523814249298264806049477299163205) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 202 = 13 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (344 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_344 :
    recurrence2Scalar0Main.coeff 344 =
      (((991165877963773 * 10 ^ 70 +
        6598612511077916435498639046259759232768136323525125796797009104287400) * 10 ^ 70 +
        1991209950413194182852426168779892222101081919125274976411461656430983) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 111 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 12 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (345 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_345 :
    recurrence2Scalar0Main.coeff 345 =
      -(((37460510217084 * 10 ^ 70 +
        8740269032486953419779362618789573898903999445601257382693315776050296) * 10 ^ 70 +
        6016762727697697325696880050227519136777357259370492244248017474842334) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 112 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 11 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (346 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_346 :
    recurrence2Scalar0Main.coeff 346 =
      (((602726363600 * 10 ^ 70 +
        8610958578091907038451716372668129121573817631895324330419097426630128) * 10 ^ 70 +
        5343559545379647073732719043526857390167110367578630058239646355753583) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 113 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 10 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (347 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_347 :
    recurrence2Scalar0Main.coeff 347 =
      (((4818180109 * 10 ^ 70 +
        0282399638340542799617167720883402601546843559163293573660239296212413) * 10 ^ 70 +
        9825950639676733065781613111687127827450043318921975478457673734063049) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 114 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 9 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (348 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_348 :
    recurrence2Scalar0Main.coeff 348 =
      -(((438609170 * 10 ^ 70 +
        9325128333910737824508385194280342896057428451800293918722851114803561) * 10 ^ 70 +
        4576335687533747032355555016690232337089829500572258651247790251710717) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 115 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 8 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (349 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_349 :
    recurrence2Scalar0Main.coeff 349 =
      (((8172799 * 10 ^ 70 +
        6123950012413100727412265048509019479547538554460281691031128174272450) * 10 ^ 70 +
        5964258203809941920987455157749944980070927143120632540925494289240835) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 116 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 7 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (350 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_350 :
    recurrence2Scalar0Main.coeff 350 =
      -(((23267 * 10 ^ 70 +
        4628521806977063470876036524762528813453373893789800010473281556938989) * 10 ^ 70 +
        6399679120100715463612576112817873889487590909168692698676188524365489) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 117 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 6 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (351 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_351 :
    recurrence2Scalar0Main.coeff 351 =
      -(((1474 * 10 ^ 70 +
        3440780243574919296972273007760464438752055502123773498790673852833363) * 10 ^ 70 +
        6193102591921077265811337102588110885102768725480386202841717884163513) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 118 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 5 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (352 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_352 :
    recurrence2Scalar0Main.coeff 352 =
      (((21 * 10 ^ 70 +
        2319869042841115332880682790464275624649178337450999649048442870876137) * 10 ^ 70 +
        3152565117386951211005041426006863859820283065959362586624600428693468) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 119 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 4 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (353 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_353 :
    recurrence2Scalar0Main.coeff 353 =
      -((31293305372524676557024745891150639522031810876573554137338255900419 * 10 ^ 70 +
        1400049358796524351528577414152284130709117878747270515747359021638320) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 120 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 3 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (354 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_354 :
    recurrence2Scalar0Main.coeff 354 =
      -((20713181893015623223490139033488029385354044770738416312170604417924 * 10 ^ 70 +
        8416239031422164179697056284921953884231071073598762761133828932634812) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 121 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 2 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (355 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_355 :
    recurrence2Scalar0Main.coeff 355 =
      ((110115340402840154865553103125902939853749353528398827795724402750 * 10 ^ 70 +
        2694590752648494252248475709608239288617568652128895827701050713255965) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 122 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 1 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (356 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_356 :
    recurrence2Scalar0Main.coeff 356 =
      ((807802576320769060018416726648574115874535301145506652419373637 * 10 ^ 70 +
        5383987404582063476412937776634467207436125219317876193557798969276968) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 123 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (357 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_357 :
    recurrence2Scalar0Main.coeff 357 =
      -((7642155161662610694273497010626492611461786383449668185377454 * 10 ^ 70 +
        0459380178364082726202922136228816741973317109549459694194382475701292) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 124 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 31 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (358 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_358 :
    recurrence2Scalar0Main.coeff 358 =
      -((11484927350220148619996609389725716204560373384835391534109 * 10 ^ 70 +
        0949066629279796549881581339673975092793038564521011137744842973036073) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 125 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 30 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (359 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_359 :
    recurrence2Scalar0Main.coeff 359 =
      ((243081737553621215362462167095323802522190806198602791555 * 10 ^ 70 +
        4592742559305681876444609197349537756287242024594767639452676402270919) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 126 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 29 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (360 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_360 :
    recurrence2Scalar0Main.coeff 360 =
      -((138804389074159281090912221504217485860870246230685047 * 10 ^ 70 +
        3056675631947611399146000121378956202356110471986372371167678793756460) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 127 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 28 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (361 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_361 :
    recurrence2Scalar0Main.coeff 361 =
      -((4127928039976001239078008300550326244775302801577056 * 10 ^ 70 +
        2021130671270522795008822251389023581832700917948751789543805727180700) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 128 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 27 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (362 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_362 :
    recurrence2Scalar0Main.coeff 362 =
      ((7516384151683937787778104407643644383674606114027 * 10 ^ 70 +
        8368942816472671629091426918855910895054272354278348836171572170272503) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 129 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 26 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (363 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_363 :
    recurrence2Scalar0Main.coeff 363 =
      ((35693243381444906732477312621541486900736908338 * 10 ^ 70 +
        6585715767980465951793869718895550325069398657943638388981673336294067) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 130 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 25 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (364 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_364 :
    recurrence2Scalar0Main.coeff 364 =
      -((110661762651615480700279477369175679514127153 * 10 ^ 70 +
        7073112234869762446999581661179269438344621139641457042003231155013853) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 131 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 24 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (365 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_365 :
    recurrence2Scalar0Main.coeff 365 =
      -((99441347900275471119781165560335029671744 * 10 ^ 70 +
        1691886432001220531170639503400153333343963922416283361033135653615874) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 132 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 23 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (366 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_366 :
    recurrence2Scalar0Main.coeff 366 =
      ((707009597677409764962189289177047336962 * 10 ^ 70 +
        9905707547758718351563195201808774554379607875789696488813424252794879) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 133 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 22 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (367 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_367 :
    recurrence2Scalar0Main.coeff 367 =
      -((520221376803460516007277918430586827 * 10 ^ 70 +
        9236935853536561204593857298200256064643407371277652599371886250461208) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 134 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 21 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (368 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_368 :
    recurrence2Scalar0Main.coeff 368 =
      -((1425192709617654737711715490143204 * 10 ^ 70 +
        2289481218137458000486012190902134419248824451550166496752033455185120) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 135 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 20 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (369 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_369 :
    recurrence2Scalar0Main.coeff 369 =
      ((2939061307591349242762614257357 * 10 ^ 70 +
        6448155083997660530491465790219818833598914937035043631559617669036109) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 136 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 19 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (370 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_370 :
    recurrence2Scalar0Main.coeff 370 =
      -((1613538330456372640861305011 * 10 ^ 70 +
        0153597802944230981951526150879124723292395520760967858238668700815727) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 137 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 18 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (371 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_371 :
    recurrence2Scalar0Main.coeff 371 =
      -((630556026267691223268693 * 10 ^ 70 +
        8871626874478879965560044674492424811090626234317765278418040840715208) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 138 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 17 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (372 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_372 :
    recurrence2Scalar0Main.coeff 372 =
      ((1118850555038714489169 * 10 ^ 70 +
        9441604927502213587793681438815520655932030274406819513044145495576504) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 139 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 16 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (373 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_373 :
    recurrence2Scalar0Main.coeff 373 =
      -((478594372476479166 * 10 ^ 70 +
        9657305567123953716575749643148400785041372009007239436980388473511261) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 140 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 15 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (374 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_374 :
    recurrence2Scalar0Main.coeff 374 =
      ((74331233785978 * 10 ^ 70 +
        4872815122769136173505292187011550314785444772333065661889836521392286) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 141 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 14 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (375 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_375 :
    recurrence2Scalar0Main.coeff 375 =
      ((1044075029 * 10 ^ 70 +
        3625593090230223430597511639000228772207868299825451134632266351740406) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 142 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 13 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (376 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_376 :
    recurrence2Scalar0Main.coeff 376 =
      -((1302666 * 10 ^ 70 +
        6570268961323618135494588441964506434113742164909965754677932648886437) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 143 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 12 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (377 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_377 :
    recurrence2Scalar0Main.coeff 377 =
      ((110 * 10 ^ 70 +
        6602885024047042195664750379155276891893810016577114454916401614756262) : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 144 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 11 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (378 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_378 :
    recurrence2Scalar0Main.coeff 378 =
      (-30097960837772564439873640634145529634968659772731937865085136387159 : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 379 = 145 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 10 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (379 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_379 :
    recurrence2Scalar0Main.coeff 379 =
      (210103072733663624353547674933011945455543547343113810137195418 : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 380 = 146 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 9 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (380 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_380 :
    recurrence2Scalar0Main.coeff 380 =
      (1529622938896234486906546024896229387378572985954582070010 : ℚ) := by
  unfold recurrence2Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 381 = 147 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 8 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
