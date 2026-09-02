/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3ShiftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B2_coeff_0
  recurrence2B2_coeff_1
  recurrence2B2_coeff_2
  recurrence2B2_coeff_3
  recurrence2B2_coeff_4
  recurrence2B2_coeff_5
  recurrence2B2_coeff_6
  recurrence2B2_coeff_7
  recurrence2B2_coeff_8
  recurrence2B2_coeff_9
  recurrence2B2_coeff_10
  recurrence2B2_coeff_11
  recurrence2B2_coeff_12
  recurrence2B2_coeff_13
  recurrence2B2_coeff_14
  recurrence2B2_coeff_15
  recurrence2B2_coeff_16
  recurrence2B2_coeff_17
  recurrence2B2_coeff_18
  recurrence2B2_coeff_19
  recurrence2B2_coeff_20
  recurrence2B2_coeff_21
  recurrence2B2_coeff_22
  recurrence2B2_coeff_23
  recurrence2B2_coeff_24
  recurrence2B2_coeff_25
  recurrence2B2_coeff_26
  recurrence2B2_coeff_27
  recurrence2B2_coeff_28
  recurrence2B2_coeff_29
  recurrence2B2_coeff_30
  recurrence2B2_coeff_31
  recurrence2B2_coeff_32
  recurrence2B2_coeff_33
  recurrence2B2_coeff_34
  recurrence2B2_coeff_35
  recurrence2B2_coeff_36
  recurrence2B2_coeff_37
  recurrence2B2_coeff_38
  recurrence2B2_coeff_39
  recurrence2B2_coeff_40
  recurrence2B2_coeff_41
  recurrence2B2_coeff_42
  recurrence2B2_coeff_43
  recurrence2B2_coeff_44
  recurrence2B2_coeff_45
  recurrence2B2_coeff_46
  recurrence2B2_coeff_47
  recurrence2B2_coeff_48
  recurrence2B2_coeff_49
  recurrence2B2_coeff_50
  recurrence2B2_coeff_51
  recurrence2B2_coeff_52
  recurrence2B2_coeff_53
  recurrence2B2_coeff_54
  recurrence2B2_coeff_55
  recurrence2B2_coeff_56
  recurrence2B2_coeff_57
  recurrence2B2_coeff_58
  recurrence2B2_coeff_59
  recurrence2B2_coeff_60
  recurrence2B2_coeff_61
  recurrence2B2_coeff_62
  recurrence2B2_coeff_63
  recurrence2B2_coeff_64
  recurrence2B2_coeff_65
  recurrence2B2_coeff_66
  recurrence2B2_coeff_67
  recurrence2B2_coeff_68
  recurrence2B2_coeff_69
  recurrence2B2_coeff_70
  recurrence2B2_coeff_71
  recurrence2B2_coeff_72
  recurrence2B2_coeff_73
  recurrence2B2_coeff_74
  recurrence2B2_coeff_75
  recurrence2B2_coeff_76
  recurrence2B2_coeff_77
  recurrence2B2_coeff_78
  recurrence2B2_coeff_79
  recurrence2B2_coeff_80
  recurrence2B2_coeff_81
  recurrence2B2_coeff_82
  recurrence2B2_coeff_83
  recurrence2B2_coeff_84
  recurrence2B2_coeff_85
  recurrence2B2_coeff_86
  recurrence2B2_coeff_87
  recurrence2B2_coeff_88
  recurrence2B2_coeff_89
  recurrence2B2_coeff_90
  recurrence2B2_coeff_91
  recurrence2B2_coeff_92
  recurrence2B2_coeff_93
  recurrence2B2_coeff_94
  recurrence2B2_coeff_95
  recurrence2B2_coeff_96
  recurrence2B2_coeff_97
  recurrence2B2_coeff_98
  recurrence2B2_coeff_99
  recurrence2B2_coeff_100
  recurrence2B2_coeff_101
  recurrence2B2_coeff_102
  recurrence2B2_coeff_103
  recurrence2B2_coeff_104
  recurrence2B2_coeff_105
  recurrence2B2_coeff_106
  recurrence2B2_coeff_107
  recurrence2B2_coeff_108
  recurrence2B2_coeff_109
  recurrence2B2_coeff_110
  recurrence2B2_coeff_111
  recurrence2B2_coeff_112
  recurrence2B2_coeff_113
  recurrence2B2_coeff_114
  recurrence2B2_coeff_115
  recurrence2B2_coeff_116
  recurrence2B2_coeff_117
  recurrence2B2_coeff_118
  recurrence2B2_coeff_119
  recurrence2B2_coeff_120
  recurrence2B2_coeff_121
  recurrence2B2_coeff_122
  recurrence2B2_coeff_123
  recurrence2B2_coeff_124
  recurrence2B2_coeff_125
  recurrence2B2_coeff_126
  recurrence2B2_coeff_127
  recurrence2B2_coeff_128
  recurrence2B2_coeff_129
  recurrence2B2_coeff_130
  recurrence2B2_coeff_131
  recurrence2B2_coeff_132
  recurrence2B2_coeff_133
  recurrence2B2_coeff_134
  recurrence2B2_coeff_135
  recurrence2B2_coeff_136
  recurrence2B2_coeff_137
  recurrence2B2_coeff_138
  recurrence2B2_coeff_139
  recurrence2B2_coeff_140
  recurrence2B2_coeff_141
  recurrence2B2_coeff_142
  recurrence2B2_coeff_143
  recurrence2B2_coeff_144
  recurrence2B2_coeff_145
  recurrence2B2_coeff_146
  recurrence2B5A6_coeff_0
  recurrence2B5A6_coeff_1
  recurrence2B5A6_coeff_2
  recurrence2B5A6_coeff_3
  recurrence2B5A6_coeff_4
  recurrence2B5A6_coeff_5
  recurrence2B5A6_coeff_6
  recurrence2B5A6_coeff_7
  recurrence2B5A6_coeff_8
  recurrence2B5A6_coeff_9
  recurrence2B5A6_coeff_10
  recurrence2B5A6_coeff_11
  recurrence2B5A6_coeff_12
  recurrence2B5A6_coeff_13
  recurrence2B5A6_coeff_14
  recurrence2B5A6_coeff_15
  recurrence2B5A6_coeff_16
  recurrence2B5A6_coeff_17
  recurrence2B5A6_coeff_18
  recurrence2B5A6_coeff_19
  recurrence2B5A6_coeff_20
  recurrence2B5A6_coeff_21
  recurrence2B5A6_coeff_22
  recurrence2B5A6_coeff_23
  recurrence2B5A6_coeff_24
  recurrence2B5A6_coeff_25
  recurrence2B5A6_coeff_26
  recurrence2B5A6_coeff_27
  recurrence2B5A6_coeff_28
  recurrence2B5A6_coeff_29
  recurrence2B5A6_coeff_30
  recurrence2B5A6_coeff_31
  recurrence2B5A6_coeff_32
  recurrence2B5A6_coeff_33
  recurrence2B5A6_coeff_34
  recurrence2B5A6_coeff_35
  recurrence2B5A6_coeff_36
  recurrence2B5A6_coeff_37
  recurrence2B5A6_coeff_38
  recurrence2B5A6_coeff_39
  recurrence2B5A6_coeff_40
  recurrence2B5A6_coeff_41
  recurrence2B5A6_coeff_42
  recurrence2B5A6_coeff_43
  recurrence2B5A6_coeff_44
  recurrence2B5A6_coeff_45
  recurrence2B5A6_coeff_46
  recurrence2B5A6_coeff_47
  recurrence2B5A6_coeff_48
  recurrence2B5A6_coeff_49
  recurrence2B5A6_coeff_50
  recurrence2B5A6_coeff_51
  recurrence2B5A6_coeff_52
  recurrence2B5A6_coeff_53
  recurrence2B5A6_coeff_54
  recurrence2B5A6_coeff_55
  recurrence2B5A6_coeff_56
  recurrence2B5A6_coeff_57
  recurrence2B5A6_coeff_58
  recurrence2B5A6_coeff_59
  recurrence2B5A6_coeff_60
  recurrence2B5A6_coeff_61
  recurrence2B5A6_coeff_62
  recurrence2B5A6_coeff_63
  recurrence2B5A6_coeff_64
  recurrence2B5A6_coeff_65
  recurrence2B5A6_coeff_66
  recurrence2B5A6_coeff_67
  recurrence2B5A6_coeff_68
  recurrence2B5A6_coeff_69
  recurrence2B5A6_coeff_70
  recurrence2B5A6_coeff_71
  recurrence2B5A6_coeff_72
  recurrence2B5A6_coeff_73
  recurrence2B5A6_coeff_74
  recurrence2B5A6_coeff_75
  recurrence2B5A6_coeff_76
  recurrence2B5A6_coeff_77
  recurrence2B5A6_coeff_78
  recurrence2B5A6_coeff_79
  recurrence2B5A6_coeff_80
  recurrence2B5A6_coeff_81
  recurrence2B5A6_coeff_82
  recurrence2B5A6_coeff_83
  recurrence2B5A6_coeff_84
  recurrence2B5A6_coeff_85
  recurrence2B5A6_coeff_86
  recurrence2B5A6_coeff_87
  recurrence2B5A6_coeff_88
  recurrence2B5A6_coeff_89
  recurrence2B5A6_coeff_90
  recurrence2B5A6_coeff_91
  recurrence2B5A6_coeff_92
  recurrence2B5A6_coeff_93
  recurrence2B5A6_coeff_94
  recurrence2B5A6_coeff_95
  recurrence2B5A6_coeff_96
  recurrence2B5A6_coeff_97
  recurrence2B5A6_coeff_98
  recurrence2B5A6_coeff_99
  recurrence2B5A6_coeff_100
  recurrence2B5A6_coeff_101
  recurrence2B5A6_coeff_102
  recurrence2B5A6_coeff_103
  recurrence2B5A6_coeff_104
  recurrence2B5A6_coeff_105
  recurrence2B5A6_coeff_106
  recurrence2B5A6_coeff_107
  recurrence2B5A6_coeff_108
  recurrence2B5A6_coeff_109
  recurrence2B5A6_coeff_110
  recurrence2B5A6_coeff_111
  recurrence2B5A6_coeff_112
  recurrence2B5A6_coeff_113
  recurrence2B5A6_coeff_114
  recurrence2B5A6_coeff_115
  recurrence2B5A6_coeff_116
  recurrence2B5A6_coeff_117
  recurrence2B5A6_coeff_118
  recurrence2B5A6_coeff_119
  recurrence2B5A6_coeff_120
  recurrence2B5A6_coeff_121
  recurrence2B5A6_coeff_122
  recurrence2B5A6_coeff_123
  recurrence2B5A6_coeff_124
  recurrence2B5A6_coeff_125
  recurrence2B5A6_coeff_126
  recurrence2B5A6_coeff_127
  recurrence2B5A6_coeff_128
  recurrence2B5A6_coeff_129
  recurrence2B5A6_coeff_130
  recurrence2B5A6_coeff_131
  recurrence2B5A6_coeff_132
  recurrence2B5A6_coeff_133
  recurrence2B5A6_coeff_134
  recurrence2B5A6_coeff_135
  recurrence2B5A6_coeff_136
  recurrence2B5A6_coeff_137
  recurrence2B5A6_coeff_138
  recurrence2B5A6_coeff_139
  recurrence2B5A6_coeff_140
  recurrence2B5A6_coeff_141
  recurrence2B5A6_coeff_142
  recurrence2B5A6_coeff_143
  recurrence2B5A6_coeff_144
  recurrence2B5A6_coeff_145
  recurrence2B5A6_coeff_146
  recurrence2B5A6_coeff_147
  recurrence2B5A6_coeff_148
  recurrence2B5A6_coeff_149
  recurrence2B5A6_coeff_150
  recurrence2B5A6_coeff_151
  recurrence2B5A6_coeff_152
  recurrence2B5A6_coeff_153
  recurrence2B5A6_coeff_154
  recurrence2B5A6_coeff_155
  recurrence2B5A6_coeff_156
  recurrence2B5A6_coeff_157
  recurrence2B5A6_coeff_158
  recurrence2B5A6_coeff_159
  recurrence2B5A6_coeff_160
  recurrence2B5A6_coeff_161
  recurrence2B5A6_coeff_162
  recurrence2B5A6_coeff_163
  recurrence2B5A6_coeff_164
  recurrence2B5A6_coeff_165
  recurrence2B5A6_coeff_166
  recurrence2B5A6_coeff_167
  recurrence2B5A6_coeff_168
  recurrence2B5A6_coeff_169
  recurrence2B5A6_coeff_170
  recurrence2B5A6_coeff_171
  recurrence2B5A6_coeff_172
  recurrence2B5A6_coeff_173
  recurrence2B5A6_coeff_174
  recurrence2B5A6_coeff_175
  recurrence2B5A6_coeff_176
  recurrence2B5A6_coeff_177
  recurrence2B5A6_coeff_178
  recurrence2B5A6_coeff_179
  recurrence2B5A6_coeff_180
  recurrence2B5A6_coeff_181
  recurrence2B5A6_coeff_182
  recurrence2B5A6_coeff_183
  recurrence2B5A6_coeff_184
  recurrence2B5A6_coeff_185
  recurrence2B5A6_coeff_186
  recurrence2B5A6_coeff_187
  recurrence2B5A6_coeff_188
  recurrence2B5A6_coeff_189
  recurrence2B5A6_coeff_190
  recurrence2B5A6_coeff_191
  recurrence2B5A6_coeff_192
  recurrence2B5A6_coeff_193
  recurrence2B5A6_coeff_194
  recurrence2B5A6_coeff_195
  recurrence2B5A6_coeff_196
  recurrence2B5A6_coeff_197
  recurrence2B5A6_coeff_198
  recurrence2B5A6_coeff_199
  recurrence2B5A6_coeff_200
  recurrence2B5A6_coeff_201
  recurrence2B5A6_coeff_202
  recurrence2B5A6_coeff_203
  recurrence2B5A6_coeff_204
  recurrence2B5A6_coeff_205
  recurrence2B5A6_coeff_206
  recurrence2B5A6_coeff_207
  recurrence2B5A6_coeff_208
  recurrence2B5A6_coeff_209
  recurrence2B5A6_coeff_210
  recurrence2B5A6_coeff_211
  recurrence2B5A6_coeff_212
  recurrence2B5A6_coeff_213
  recurrence2B5A6_coeff_214
  recurrence2B5A6_coeff_215
  recurrence2B5A6_coeff_216
  recurrence2B5A6_coeff_217
  recurrence2B5A6_coeff_218
  recurrence2B5A6_coeff_219
  recurrence2B5A6_coeff_220
  recurrence2B5A6_coeff_221
  recurrence2B5A6_coeff_222
  recurrence2B5A6_coeff_223
  recurrence2B5A6_coeff_224
  recurrence2B5A6_coeff_225
  recurrence2B5A6_coeff_226
  recurrence2B5A6_coeff_227
  recurrence2B5A6_coeff_228
  recurrence2B5A6_coeff_229

private theorem recurrence2Scalar3Shift_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (336 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_336 :
    recurrence2Scalar3Shift.coeff 336 =
      -(((13247371014 * 10 ^ 70 +
        8308539211999096722388485415962410364185872180514673753624826899695535) * 10 ^ 70 +
        6985533458148373575856872063142775546233871476752823882682530067146651) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 107 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 8 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (337 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_337 :
    recurrence2Scalar3Shift.coeff 337 =
      -(((171251846 * 10 ^ 70 +
        0058707341757629495054623911498632908092134146569117089231304209554615) * 10 ^ 70 +
        5941924208081933784775686390960777820656383733673613220073438625220822) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 108 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 7 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (338 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_338 :
    recurrence2Scalar3Shift.coeff 338 =
      (((7729130 * 10 ^ 70 +
        6832879553047241271067340599446401415965589416913378221228515693782507) * 10 ^ 70 +
        8909107385958603360722874737238722685752069121743241937981853313274324) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 109 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 6 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (339 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_339 :
    recurrence2Scalar3Shift.coeff 339 =
      -(((79467 * 10 ^ 70 +
        2281802734705075892003668072950578076954424970453013313294235048488450) * 10 ^ 70 +
        4395690913695422220199081335852946141454146000772407873609878294132236) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 110 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 5 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (340 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_340 :
    recurrence2Scalar3Shift.coeff 340 =
      -(((466 * 10 ^ 70 +
        4192822789109021217301851965792944087098548800274137403540648157776335) * 10 ^ 70 +
        4563027060934648235009782246294518642705732782008959115108461183101211) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 111 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 4 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (341 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_341 :
    recurrence2Scalar3Shift.coeff 341 =
      (((15 * 10 ^ 70 +
        7644598980336030532757602447541890761383613873306135639365217265448312) * 10 ^ 70 +
        6799391734214307022192141413059846821452046111464051111281872643190236) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 112 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 3 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (342 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_342 :
    recurrence2Scalar3Shift.coeff 342 =
      -((627626893075892454386287886836668899936096622397991275063461847421196 * 10 ^ 70 +
        6454577332777221710015989226024063462470695218096869255278376080024819) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 113 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 2 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (343 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_343 :
    recurrence2Scalar3Shift.coeff 343 =
      -((9930499660016114127638051725177304927415096746931535857697046224674 * 10 ^ 70 +
        1356677144963770492598277625363244658674582967419888403805748315475559) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 114 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 1 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (344 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_344 :
    recurrence2Scalar3Shift.coeff 344 =
      ((81826728700567318714040865446037735878136832542297240542638701158 * 10 ^ 70 +
        2807471221351396070560066258490280574202332770110168739958257966099845) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 115 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (345 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_345 :
    recurrence2Scalar3Shift.coeff 345 =
      ((257301846929008225471371544164409318792275984656306618155901664 * 10 ^ 70 +
        4550066869923006596881721199338682053527518167638310547766548320008541) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 116 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 31 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (346 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_346 :
    recurrence2Scalar3Shift.coeff 346 =
      -((3889692393618105503261552997279898198386528612155066406722597 * 10 ^ 70 +
        7693397951904969470419032676373995610746940461330205348873839513556655) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 117 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 30 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (347 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_347 :
    recurrence2Scalar3Shift.coeff 347 =
      -((740989285024878836121972638973176078254135445440231290242 * 10 ^ 70 +
        2861482076530659104164346878315813765031244056657751622108704315531316) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 118 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 29 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (348 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_348 :
    recurrence2Scalar3Shift.coeff 348 =
      ((96543156598210164959306376260356299965513643544875411100 * 10 ^ 70 +
        7479247137229142884484108844962851190008129305776677889612155423853661) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 119 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 28 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (349 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_349 :
    recurrence2Scalar3Shift.coeff 349 =
      -((117329047297662773853458320093103492519261978741542481 * 10 ^ 70 +
        2124895726658445545673840365825765160183476775091250050414022597989514) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 120 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 27 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (350 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_350 :
    recurrence2Scalar3Shift.coeff 350 =
      -((1308762101161586506729729642070179299513105417560564 * 10 ^ 70 +
        9139033331594766144437161435722703992529313876594439203128841186741489) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 121 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 26 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (351 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_351 :
    recurrence2Scalar3Shift.coeff 351 =
      ((2969055682104249693033070283909213065285837969325 * 10 ^ 70 +
        3375776272007091730558483455437939107102155080623410248278471689598223) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 122 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 25 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (352 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_352 :
    recurrence2Scalar3Shift.coeff 352 =
      ((8621666411570524824476412825759622122946989636 * 10 ^ 70 +
        5420877912349702067347227654019087734004423696389500428236972240822044) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 123 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 24 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (353 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_353 :
    recurrence2Scalar3Shift.coeff 353 =
      -((31943216475720628569317190242591194848812386 * 10 ^ 70 +
        2196373438556348006578685190548429672736651147459732028848500123264736) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 124 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 23 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (354 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_354 :
    recurrence2Scalar3Shift.coeff 354 =
      -((9619462725666532684998940447891910282728 * 10 ^ 70 +
        0199653221911724033690506931440753315703795116908561669089088199855243) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 125 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 22 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (355 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_355 :
    recurrence2Scalar3Shift.coeff 355 =
      ((149364870373557463259330379543222616751 * 10 ^ 70 +
        7723818465477456647383307972384702245162566833831079936615132711976765) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 126 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 21 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (356 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_356 :
    recurrence2Scalar3Shift.coeff 356 =
      -((154717701436839856146371287802271709 * 10 ^ 70 +
        1536783776051650527281760246654030936687451148034203772965148089412056) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 127 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 20 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (357 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_357 :
    recurrence2Scalar3Shift.coeff 357 =
      -((153945028770103129077717567469866 * 10 ^ 70 +
        2100203697508895887441526848438226328432919045287365977274681632426877) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 128 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 19 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (358 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_358 :
    recurrence2Scalar3Shift.coeff 358 =
      ((417990921122235296519761732630 * 10 ^ 70 +
        0884748575913449004617692563562344812670556925242444438558294642939863) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 129 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 18 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (359 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_359 :
    recurrence2Scalar3Shift.coeff 359 =
      -((284474063529363702207430955 * 10 ^ 70 +
        3290641655238165460358128517580832771568586381193365621498594407387534) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 130 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 17 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (360 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_360 :
    recurrence2Scalar3Shift.coeff 360 =
      ((20142920343341738292875 * 10 ^ 70 +
        0991048049413455595692938797710041707775497587375658806592795169062073) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 131 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 16 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (361 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_361 :
    recurrence2Scalar3Shift.coeff 361 =
      ((59883243616274239521 * 10 ^ 70 +
        6586506244118301054368294398929001493128977325780572736350802801938219) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 132 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 15 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (362 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_362 :
    recurrence2Scalar3Shift.coeff 362 =
      -((26999596876736381 * 10 ^ 70 +
        6330668664512368831426845672176168766310745696891890530854996402178125) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 133 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 14 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (363 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_363 :
    recurrence2Scalar3Shift.coeff 363 =
      ((4182527216633 * 10 ^ 70 +
        9586209700382871870430823030626200207211332330611846469443862095902286) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 134 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 13 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (364 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_364 :
    recurrence2Scalar3Shift.coeff 364 =
      -((140237945 * 10 ^ 70 +
        1849784473461775035477856139875735881958807820661374535752697602049867) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 135 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 12 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (365 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_365 :
    recurrence2Scalar3Shift.coeff 365 =
      -((19222 * 10 ^ 70 +
        4723116937040079734726739575414717689070899626466290896544913650486945) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 136 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 11 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (366 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_366 :
    recurrence2Scalar3Shift.coeff 366 =
      ((1 * 10 ^ 70 +
        5171791846473585029461913609637339901287956700507924355201482925353965) : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 137 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 10 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (367 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_367 :
    recurrence2Scalar3Shift.coeff 367 =
      (-326748467231985099277039007699553112269302401102927411775581648598 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 138 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 9 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (368 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_368 :
    recurrence2Scalar3Shift.coeff 368 =
      (1866921889427777477585165710501847736200764144627540842918583 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 139 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 8 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (369 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_369 :
    recurrence2Scalar3Shift.coeff 369 =
      (1992955521863482669546903058786574235939405405654698452 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 140 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 7 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (370 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_370 :
    recurrence2Scalar3Shift.coeff 370 =
      (-22194740933985694963963876171341280510094357767775 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 141 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 6 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (371 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_371 :
    recurrence2Scalar3Shift.coeff 371 =
      (18495588673549012232517070907111886696608400 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 142 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 5 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (372 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_372 :
    recurrence2Scalar3Shift.coeff 372 =
      (-2428415422479462826016467479132468682 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 143 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 4 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (373 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_373 :
    recurrence2Scalar3Shift.coeff 373 =
      (14109381873722360030037538062 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 144 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 3 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (374 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_374 :
    recurrence2Scalar3Shift.coeff 374 =
      (14623435900183798807 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 145 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 2 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Shift_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient2.coeff x * recurrence2B5A6.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Shift_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2B5A6.coeff (375 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Shift_coeff_375 :
    recurrence2Scalar3Shift.coeff 375 =
      (-22256050974 : ℚ) := by
  unfold recurrence2Scalar3Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 146 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 1 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Shift_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Shift_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
