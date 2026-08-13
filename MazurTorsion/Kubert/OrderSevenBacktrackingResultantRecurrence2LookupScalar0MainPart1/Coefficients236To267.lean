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

private theorem recurrence2Scalar0Main_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (236 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_236 :
    recurrence2Scalar0Main.coeff 236 =
      ((((6930 * 10 ^ 70 +
        4173725646603797473254053903337855014328521726276667926506144738042480) * 10 ^ 70 +
        0261597618626137237027825898765539348803040420961858141675165436495988) * 10 ^ 70 +
        2161621584991166214931842165229757456195800137678119857082984446870423) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 24 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (237 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_237 :
    recurrence2Scalar0Main.coeff 237 =
      -((((7619 * 10 ^ 70 +
        3156750023892765688144604067308306393571625781424435887575872033335083) * 10 ^ 70 +
        0380227255685731935058463380600560564375412634350746944930333525735479) * 10 ^ 70 +
        8809339239421559738695576304680460790891655866777909319028446899056378) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 23 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (238 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_238 :
    recurrence2Scalar0Main.coeff 238 =
      ((((7968 * 10 ^ 70 +
        1880087459132719470155006619622305556673073026250372214050783947347104) * 10 ^ 70 +
        2795596537291931758881408380795090400916155550175630695995584856213274) * 10 ^ 70 +
        6167811604499954049612869901762535271531559503508705230144591121640961) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 22 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (239 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_239 :
    recurrence2Scalar0Main.coeff 239 =
      -((((7914 * 10 ^ 70 +
        4579601491421491845612576889622525597284493388979719681324151278063194) * 10 ^ 70 +
        2357499583185049656476576565085460431877762347024784216805954032000630) * 10 ^ 70 +
        5362474073128633898477271944250402107623691286067142386596644765164605) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 21 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (240 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_240 :
    recurrence2Scalar0Main.coeff 240 =
      ((((7440 * 10 ^ 70 +
        1531600139951903538509441922659576795050022122103119648540303282699869) * 10 ^ 70 +
        6678482031576215818742232434168640586332079389224546757853774491006555) * 10 ^ 70 +
        0274715935087210440186302607891306575906370741026629183398205006848082) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 20 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (241 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_241 :
    recurrence2Scalar0Main.coeff 241 =
      -((((6576 * 10 ^ 70 +
        5596743071976759773457506446192051248786633232856597780233529694433647) * 10 ^ 70 +
        9812341014331789970856273942157838973041122893131841483086154355186579) * 10 ^ 70 +
        0130939094921074041375348156527929423086197236170808345119376646746407) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 19 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (242 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_242 :
    recurrence2Scalar0Main.coeff 242 =
      ((((5400 * 10 ^ 70 +
        3974574836992087256506124201275508576291482999505494580579791369663393) * 10 ^ 70 +
        5600686745333201705002935382481279641840939553033631250232525220693823) * 10 ^ 70 +
        1993593984935747379167775633504905205183541593861443992022257825969538) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 18 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (243 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_243 :
    recurrence2Scalar0Main.coeff 243 =
      -((((4022 * 10 ^ 70 +
        2649343519442198979984486010068818792191653108467592470861464355087849) * 10 ^ 70 +
        8681613700458990931207219267896563928313572217653034365647482520783886) * 10 ^ 70 +
        0745336323865454300550937151289972752658136003185768328258006555353802) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 17 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (244 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_244 :
    recurrence2Scalar0Main.coeff 244 =
      ((((2569 * 10 ^ 70 +
        7987712086180369948316724940080851392770792323999870470045082390433937) * 10 ^ 70 +
        7648631805947750884962294416707810596549661470862666611733859096299246) * 10 ^ 70 +
        1860398975354197665865371350055320548780873370006803119756667569968091) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 16 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_244_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (245 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_245 :
    recurrence2Scalar0Main.coeff 245 =
      -((((1169 * 10 ^ 70 +
        0326239843254896254871808187778903353386946620907224072206790142694907) * 10 ^ 70 +
        0947603733774240118374451954562626571883403082982547627049083640645567) * 10 ^ 70 +
        2700957872219631582103876106748600210200555698825685054605344357216177) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 15 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_245_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (246 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_246 :
    recurrence2Scalar0Main.coeff 246 =
      -((((72 * 10 ^ 70 +
        4224285428941169421833560974855257537318054234501373359734180053932856) * 10 ^ 70 +
        4029621916973183571071067322358568828063212616695652205023256033574550) * 10 ^ 70 +
        2512528940683795681222694948535655648394918187956741889282757895731069) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 14 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (247 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_247 :
    recurrence2Scalar0Main.coeff 247 =
      ((((1077 * 10 ^ 70 +
        4765492552769213787518229423080879484774750685389368142299355973746280) * 10 ^ 70 +
        7247210074646100976514875627683655671845995441314870034661797188640770) * 10 ^ 70 +
        1438070689768734477331893242973919986576021544238137738825166264397121) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 106 = 13 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (248 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_248 :
    recurrence2Scalar0Main.coeff 248 =
      -((((1805 * 10 ^ 70 +
        3499657765891824996657390294486409613979806712609974219874949869062020) * 10 ^ 70 +
        9594571344416073950102379064061173183623618773797762763298326985963927) * 10 ^ 70 +
        9504272120638955006365313455956561201923931968116930341604165913114344) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rhs
    rw [show 106 = 12 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (249 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_249 :
    recurrence2Scalar0Main.coeff 249 =
      ((((2250 * 10 ^ 70 +
        9556144096366509951776069611593669937614307764257391231146000044316658) * 10 ^ 70 +
        6776126144505827876102302973369111718803250974849206758111878967985377) * 10 ^ 70 +
        1530551859894547637756348667609614220115542097437386676437485290038262) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 11 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (250 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_250 :
    recurrence2Scalar0Main.coeff 250 =
      -((((2439 * 10 ^ 70 +
        0586590698317517180393411672059877482100576975246455418729265844941807) * 10 ^ 70 +
        0098879937594713696767026423434361424267408935688601033574756426779860) * 10 ^ 70 +
        1453721206125613628869620271960395629398868601261679361238014587997259) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 10 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (251 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_251 :
    recurrence2Scalar0Main.coeff 251 =
      ((((2415 * 10 ^ 70 +
        1895545828719948640176410700200783116164203182015841867261747438127542) * 10 ^ 70 +
        9822662418643417196980666603358896865814188262223636025502427665131257) * 10 ^ 70 +
        5961596323899507759734718060744916650059963805224559573604749037973492) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 9 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (252 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_252 :
    recurrence2Scalar0Main.coeff 252 =
      -((((2235 * 10 ^ 70 +
        5013111489289747142972665394356346263706976439932039657184221756906441) * 10 ^ 70 +
        1718556939761761673699716856801551341630699235565350326892718315303572) * 10 ^ 70 +
        2917233268183608088882802682042637114603943271241508349406210828965238) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 8 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (253 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_253 :
    recurrence2Scalar0Main.coeff 253 =
      ((((1957 * 10 ^ 70 +
        4707689098842591460122309542485292618108447954895595102743829734250992) * 10 ^ 70 +
        8636301841410299376422764735323001603553527379248008183573626967751154) * 10 ^ 70 +
        5055410917214927237295275921009399914346730485537717693653009075939413) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 7 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (254 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_254 :
    recurrence2Scalar0Main.coeff 254 =
      -((((1632 * 10 ^ 70 +
        7327214547658620851019538196447443115845704417385194904778584554843269) * 10 ^ 70 +
        4485451947123551689120657945625607814066413634546869057669625820902802) * 10 ^ 70 +
        6516925752065930364641278346550054434737637247030835725264394246245631) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 6 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (255 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_255 :
    recurrence2Scalar0Main.coeff 255 =
      ((((1302 * 10 ^ 70 +
        6221107580814209379408944936091550827741855536084996253911502754069284) * 10 ^ 70 +
        5553989100268914634386650772554421749355877920676675464875558540840404) * 10 ^ 70 +
        9931614462846199713936376875279561894763795974369657801339161035566274) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 5 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (256 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_256 :
    recurrence2Scalar0Main.coeff 256 =
      -((((996 * 10 ^ 70 +
        3669867699707652819923308332994514435957761479325091817128479025088409) * 10 ^ 70 +
        7391641521222783544937939168878609140927902875812956524797266749392030) * 10 ^ 70 +
        9509310263475723889671825945474112563873184313230710880500337310295497) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 4 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (257 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_257 :
    recurrence2Scalar0Main.coeff 257 =
      ((((731 * 10 ^ 70 +
        4353295244741773701314552988276226343683349416412442170101917335041903) * 10 ^ 70 +
        4166357604701949963728592862687669718247881947310319877812817126767473) * 10 ^ 70 +
        2790187316605408247945192952840703292347502048110999955210771994684912) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 3 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (258 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_258 :
    recurrence2Scalar0Main.coeff 258 =
      -((((515 * 10 ^ 70 +
        3255426890082479172223423067384686394059149099188246217698336759735016) * 10 ^ 70 +
        0891416181089077170049821059297517765451274674953009223804292794848639) * 10 ^ 70 +
        9922961524557434114633366719361487371451228586311961285144112067203852) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 2 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (259 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_259 :
    recurrence2Scalar0Main.coeff 259 =
      ((((348 * 10 ^ 70 +
        0752519827901344953807036629314212442858951569027251522490359929808017) * 10 ^ 70 +
        2621865392886168239178960829025250289804009167828796912613114313017846) * 10 ^ 70 +
        6592708199487670800889881525730113695761946990612909412961254308776297) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 1 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (260 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_260 :
    recurrence2Scalar0Main.coeff 260 =
      -((((224 * 10 ^ 70 +
        8837573986826452946142288473299342780682778748213584638659528606354279) * 10 ^ 70 +
        2248843825181015145913252775425893639089414108020283032779560288345585) * 10 ^ 70 +
        7300656080042793830518651698560898189010595643757307788072736887791318) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (261 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_261 :
    recurrence2Scalar0Main.coeff 261 =
      ((((138 * 10 ^ 70 +
        4303759736970617650222105071407614121758233134213052532888294699736463) * 10 ^ 70 +
        7759676370247741706941702258867872979135163224956940315154388516088513) * 10 ^ 70 +
        2057447979530230374919504268329524400879540624516043919074550031734839) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 31 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (262 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_262 :
    recurrence2Scalar0Main.coeff 262 =
      -((((80 * 10 ^ 70 +
        6653269756217030035592055576109107398724674575182937569175636954753022) * 10 ^ 70 +
        6739843509570528223273160928782804419090373516906946035554777795791610) * 10 ^ 70 +
        4986726526360584634965942668492816987029462256185831389705319661611950) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 30 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (263 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_263 :
    recurrence2Scalar0Main.coeff 263 =
      ((((44 * 10 ^ 70 +
        0129453667092275411785688931244639006969715975267122005072936471121913) * 10 ^ 70 +
        3621889650466577444270792162588302733338277872481045424250024314837659) * 10 ^ 70 +
        4229947597000601211874356144820842123324029375537131457403410882859890) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 29 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (264 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_264 :
    recurrence2Scalar0Main.coeff 264 =
      -((((22 * 10 ^ 70 +
        0405844279578020409713525305739374335207800623986062875164551037694727) * 10 ^ 70 +
        3579532304966288459325161934529402807312341081570730226232331172772663) * 10 ^ 70 +
        0811115471689136805633962261935442610756557198546560505236514144873718) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 28 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (265 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_265 :
    recurrence2Scalar0Main.coeff 265 =
      ((((9 * 10 ^ 70 +
        7086748920823271808442767326247396780913584213007099657764283933304324) * 10 ^ 70 +
        0212534257943814552278589011587837766224992548951489283924398748878732) * 10 ^ 70 +
        6658068052703452924796171834538547727269365237428088348010289490151214) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 27 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (266 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_266 :
    recurrence2Scalar0Main.coeff 266 =
      -((((3 * 10 ^ 70 +
        3365331324918413777634279786813613192211982954695808994312322066887094) * 10 ^ 70 +
        9681597096124210757327594668232510173627228642794394884370591728720595) * 10 ^ 70 +
        5906520247245691495050509605290402783810510020598640339960467377505731) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 26 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Main_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient0.coeff x * recurrence2QuotientConstant.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Main_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2QuotientConstant.coeff (267 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Main_coeff_267 :
    recurrence2Scalar0Main.coeff 267 =
      (((4078525747702871333145303949838237101513457577788508175297879326527292 * 10 ^ 70 +
        2716983098387136730991074443700323417514126375179897402368615111359321) * 10 ^ 70 +
        2177956376441422322843736295989455559173808937697208614071978048450404) : ℚ) := by
  unfold recurrence2Scalar0Main
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
    rw [show 138 = 25 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Main_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Main_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
