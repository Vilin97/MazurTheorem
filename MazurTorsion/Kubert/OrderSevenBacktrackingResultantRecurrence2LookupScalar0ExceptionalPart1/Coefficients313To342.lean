/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2ExceptionalProduct_coeff_0
  recurrence2ExceptionalProduct_coeff_1
  recurrence2ExceptionalProduct_coeff_2
  recurrence2ExceptionalProduct_coeff_3
  recurrence2ExceptionalProduct_coeff_4
  recurrence2ExceptionalProduct_coeff_5
  recurrence2ExceptionalProduct_coeff_6
  recurrence2ExceptionalProduct_coeff_7
  recurrence2ExceptionalProduct_coeff_8
  recurrence2ExceptionalProduct_coeff_9
  recurrence2ExceptionalProduct_coeff_10
  recurrence2ExceptionalProduct_coeff_11
  recurrence2ExceptionalProduct_coeff_12
  recurrence2ExceptionalProduct_coeff_13
  recurrence2ExceptionalProduct_coeff_14
  recurrence2ExceptionalProduct_coeff_15
  recurrence2ExceptionalProduct_coeff_16
  recurrence2ExceptionalProduct_coeff_17
  recurrence2ExceptionalProduct_coeff_18
  recurrence2ExceptionalProduct_coeff_19
  recurrence2ExceptionalProduct_coeff_20
  recurrence2ExceptionalProduct_coeff_21
  recurrence2ExceptionalProduct_coeff_22
  recurrence2ExceptionalProduct_coeff_23
  recurrence2ExceptionalProduct_coeff_24
  recurrence2ExceptionalProduct_coeff_25
  recurrence2ExceptionalProduct_coeff_26
  recurrence2ExceptionalProduct_coeff_27
  recurrence2ExceptionalProduct_coeff_28
  recurrence2ExceptionalProduct_coeff_29
  recurrence2ExceptionalProduct_coeff_30
  recurrence2ExceptionalProduct_coeff_31
  recurrence2ExceptionalProduct_coeff_32
  recurrence2ExceptionalProduct_coeff_33
  recurrence2ExceptionalProduct_coeff_34
  recurrence2ExceptionalProduct_coeff_35
  recurrence2ExceptionalProduct_coeff_36
  recurrence2ExceptionalProduct_coeff_37
  recurrence2ExceptionalProduct_coeff_38
  recurrence2ExceptionalProduct_coeff_39
  recurrence2ExceptionalProduct_coeff_40
  recurrence2ExceptionalProduct_coeff_41
  recurrence2ExceptionalProduct_coeff_42
  recurrence2ExceptionalProduct_coeff_43
  recurrence2ExceptionalProduct_coeff_44
  recurrence2ExceptionalProduct_coeff_45
  recurrence2ExceptionalProduct_coeff_46
  recurrence2ExceptionalProduct_coeff_47
  recurrence2ExceptionalProduct_coeff_48
  recurrence2ExceptionalProduct_coeff_49
  recurrence2ExceptionalProduct_coeff_50
  recurrence2ExceptionalProduct_coeff_51
  recurrence2ExceptionalProduct_coeff_52
  recurrence2ExceptionalProduct_coeff_53
  recurrence2ExceptionalProduct_coeff_54
  recurrence2ExceptionalProduct_coeff_55
  recurrence2ExceptionalProduct_coeff_56
  recurrence2ExceptionalProduct_coeff_57
  recurrence2ExceptionalProduct_coeff_58
  recurrence2ExceptionalProduct_coeff_59
  recurrence2ExceptionalProduct_coeff_60
  recurrence2ExceptionalProduct_coeff_61
  recurrence2ExceptionalProduct_coeff_62
  recurrence2ExceptionalProduct_coeff_63
  recurrence2ExceptionalProduct_coeff_64
  recurrence2ExceptionalProduct_coeff_65
  recurrence2ExceptionalProduct_coeff_66
  recurrence2ExceptionalProduct_coeff_67
  recurrence2ExceptionalProduct_coeff_68
  recurrence2ExceptionalProduct_coeff_69
  recurrence2ExceptionalProduct_coeff_70
  recurrence2ExceptionalProduct_coeff_71
  recurrence2ExceptionalProduct_coeff_72
  recurrence2ExceptionalProduct_coeff_73
  recurrence2ExceptionalProduct_coeff_74
  recurrence2ExceptionalProduct_coeff_75
  recurrence2ExceptionalProduct_coeff_76
  recurrence2ExceptionalProduct_coeff_77
  recurrence2ExceptionalProduct_coeff_78
  recurrence2ExceptionalProduct_coeff_79
  recurrence2ExceptionalProduct_coeff_80
  recurrence2ExceptionalProduct_coeff_81
  recurrence2ExceptionalProduct_coeff_82
  recurrence2ExceptionalProduct_coeff_83
  recurrence2ExceptionalProduct_coeff_84
  recurrence2ExceptionalProduct_coeff_85
  recurrence2ExceptionalProduct_coeff_86
  recurrence2ExceptionalProduct_coeff_87
  recurrence2ExceptionalProduct_coeff_88
  recurrence2ExceptionalProduct_coeff_89
  recurrence2ExceptionalProduct_coeff_90
  recurrence2ExceptionalProduct_coeff_91
  recurrence2ExceptionalProduct_coeff_92
  recurrence2ExceptionalProduct_coeff_93
  recurrence2ExceptionalProduct_coeff_94
  recurrence2ExceptionalProduct_coeff_95
  recurrence2ExceptionalProduct_coeff_96
  recurrence2ExceptionalProduct_coeff_97
  recurrence2ExceptionalProduct_coeff_98
  recurrence2ExceptionalProduct_coeff_99
  recurrence2ExceptionalProduct_coeff_100
  recurrence2ExceptionalProduct_coeff_101
  recurrence2ExceptionalProduct_coeff_102
  recurrence2ExceptionalProduct_coeff_103
  recurrence2ExceptionalProduct_coeff_104
  recurrence2ExceptionalProduct_coeff_105
  recurrence2ExceptionalProduct_coeff_106
  recurrence2ExceptionalProduct_coeff_107
  recurrence2ExceptionalProduct_coeff_108
  recurrence2ExceptionalProduct_coeff_109
  recurrence2ExceptionalProduct_coeff_110
  recurrence2ExceptionalProduct_coeff_111
  recurrence2ExceptionalProduct_coeff_112
  recurrence2ExceptionalProduct_coeff_113
  recurrence2ExceptionalProduct_coeff_114
  recurrence2ExceptionalProduct_coeff_115
  recurrence2ExceptionalProduct_coeff_116
  recurrence2ExceptionalProduct_coeff_117
  recurrence2ExceptionalProduct_coeff_118
  recurrence2ExceptionalProduct_coeff_119
  recurrence2ExceptionalProduct_coeff_120
  recurrence2ExceptionalProduct_coeff_121
  recurrence2ExceptionalProduct_coeff_122
  recurrence2ExceptionalProduct_coeff_123
  recurrence2ExceptionalProduct_coeff_124
  recurrence2ExceptionalProduct_coeff_125
  recurrence2ExceptionalProduct_coeff_126
  recurrence2ExceptionalProduct_coeff_127
  recurrence2ExceptionalProduct_coeff_128
  recurrence2ExceptionalProduct_coeff_129
  recurrence2ExceptionalProduct_coeff_130
  recurrence2ExceptionalProduct_coeff_131
  recurrence2ExceptionalProduct_coeff_132
  recurrence2ExceptionalProduct_coeff_133
  recurrence2ExceptionalProduct_coeff_134
  recurrence2ExceptionalProduct_coeff_135
  recurrence2ExceptionalProduct_coeff_136
  recurrence2ExceptionalProduct_coeff_137
  recurrence2ExceptionalProduct_coeff_138
  recurrence2ExceptionalProduct_coeff_139
  recurrence2ExceptionalProduct_coeff_140
  recurrence2ExceptionalProduct_coeff_141
  recurrence2ExceptionalProduct_coeff_142
  recurrence2ExceptionalProduct_coeff_143
  recurrence2ExceptionalProduct_coeff_144
  recurrence2ExceptionalProduct_coeff_145
  recurrence2ExceptionalProduct_coeff_146
  recurrence2ExceptionalProduct_coeff_147
  recurrence2ExceptionalProduct_coeff_148
  recurrence2ExceptionalProduct_coeff_149
  recurrence2ExceptionalProduct_coeff_150
  recurrence2ExceptionalProduct_coeff_151
  recurrence2ExceptionalProduct_coeff_152
  recurrence2ExceptionalProduct_coeff_153
  recurrence2ExceptionalProduct_coeff_154
  recurrence2ExceptionalProduct_coeff_155
  recurrence2ExceptionalProduct_coeff_156
  recurrence2ExceptionalProduct_coeff_157
  recurrence2ExceptionalProduct_coeff_158
  recurrence2ExceptionalProduct_coeff_159
  recurrence2ExceptionalProduct_coeff_160
  recurrence2ExceptionalProduct_coeff_161
  recurrence2ExceptionalProduct_coeff_162
  recurrence2ExceptionalProduct_coeff_163
  recurrence2ExceptionalProduct_coeff_164
  recurrence2ExceptionalProduct_coeff_165
  recurrence2ExceptionalProduct_coeff_166
  recurrence2ExceptionalProduct_coeff_167
  recurrence2ExceptionalProduct_coeff_168
  recurrence2ExceptionalProduct_coeff_169
  recurrence2ExceptionalProduct_coeff_170
  recurrence2ExceptionalProduct_coeff_171
  recurrence2ExceptionalProduct_coeff_172
  recurrence2ExceptionalProduct_coeff_173
  recurrence2ExceptionalProduct_coeff_174
  recurrence2ExceptionalProduct_coeff_175
  recurrence2ExceptionalProduct_coeff_176
  recurrence2ExceptionalProduct_coeff_177
  recurrence2ExceptionalProduct_coeff_178
  recurrence2ExceptionalProduct_coeff_179
  recurrence2ExceptionalProduct_coeff_180
  recurrence2ExceptionalProduct_coeff_181
  recurrence2ExceptionalProduct_coeff_182
  recurrence2ExceptionalProduct_coeff_183
  recurrence2ExceptionalProduct_coeff_184
  recurrence2ExceptionalProduct_coeff_185
  recurrence2ExceptionalProduct_coeff_186
  recurrence2ExceptionalProduct_coeff_187
  recurrence2ExceptionalProduct_coeff_188
  recurrence2ExceptionalProduct_coeff_189
  recurrence2ExceptionalProduct_coeff_190
  recurrence2ExceptionalProduct_coeff_191
  recurrence2ExceptionalProduct_coeff_192
  recurrence2ExceptionalProduct_coeff_193
  recurrence2C0_coeff_0
  recurrence2C0_coeff_1
  recurrence2C0_coeff_2
  recurrence2C0_coeff_3
  recurrence2C0_coeff_4
  recurrence2C0_coeff_5
  recurrence2C0_coeff_6
  recurrence2C0_coeff_7
  recurrence2C0_coeff_8
  recurrence2C0_coeff_9
  recurrence2C0_coeff_10
  recurrence2C0_coeff_11
  recurrence2C0_coeff_12
  recurrence2C0_coeff_13
  recurrence2C0_coeff_14
  recurrence2C0_coeff_15
  recurrence2C0_coeff_16
  recurrence2C0_coeff_17
  recurrence2C0_coeff_18
  recurrence2C0_coeff_19
  recurrence2C0_coeff_20
  recurrence2C0_coeff_21
  recurrence2C0_coeff_22
  recurrence2C0_coeff_23
  recurrence2C0_coeff_24
  recurrence2C0_coeff_25
  recurrence2C0_coeff_26
  recurrence2C0_coeff_27
  recurrence2C0_coeff_28
  recurrence2C0_coeff_29
  recurrence2C0_coeff_30
  recurrence2C0_coeff_31
  recurrence2C0_coeff_32
  recurrence2C0_coeff_33
  recurrence2C0_coeff_34
  recurrence2C0_coeff_35
  recurrence2C0_coeff_36
  recurrence2C0_coeff_37
  recurrence2C0_coeff_38
  recurrence2C0_coeff_39
  recurrence2C0_coeff_40
  recurrence2C0_coeff_41
  recurrence2C0_coeff_42
  recurrence2C0_coeff_43
  recurrence2C0_coeff_44
  recurrence2C0_coeff_45
  recurrence2C0_coeff_46
  recurrence2C0_coeff_47
  recurrence2C0_coeff_48
  recurrence2C0_coeff_49
  recurrence2C0_coeff_50
  recurrence2C0_coeff_51
  recurrence2C0_coeff_52
  recurrence2C0_coeff_53
  recurrence2C0_coeff_54
  recurrence2C0_coeff_55
  recurrence2C0_coeff_56
  recurrence2C0_coeff_57
  recurrence2C0_coeff_58
  recurrence2C0_coeff_59
  recurrence2C0_coeff_60
  recurrence2C0_coeff_61
  recurrence2C0_coeff_62
  recurrence2C0_coeff_63
  recurrence2C0_coeff_64
  recurrence2C0_coeff_65
  recurrence2C0_coeff_66
  recurrence2C0_coeff_67
  recurrence2C0_coeff_68
  recurrence2C0_coeff_69
  recurrence2C0_coeff_70
  recurrence2C0_coeff_71
  recurrence2C0_coeff_72
  recurrence2C0_coeff_73
  recurrence2C0_coeff_74
  recurrence2C0_coeff_75
  recurrence2C0_coeff_76
  recurrence2C0_coeff_77
  recurrence2C0_coeff_78
  recurrence2C0_coeff_79
  recurrence2C0_coeff_80
  recurrence2C0_coeff_81
  recurrence2C0_coeff_82
  recurrence2C0_coeff_83
  recurrence2C0_coeff_84
  recurrence2C0_coeff_85
  recurrence2C0_coeff_86
  recurrence2C0_coeff_87
  recurrence2C0_coeff_88
  recurrence2C0_coeff_89
  recurrence2C0_coeff_90
  recurrence2C0_coeff_91
  recurrence2C0_coeff_92
  recurrence2C0_coeff_93
  recurrence2C0_coeff_94
  recurrence2C0_coeff_95
  recurrence2C0_coeff_96
  recurrence2C0_coeff_97
  recurrence2C0_coeff_98
  recurrence2C0_coeff_99
  recurrence2C0_coeff_100
  recurrence2C0_coeff_101
  recurrence2C0_coeff_102
  recurrence2C0_coeff_103
  recurrence2C0_coeff_104
  recurrence2C0_coeff_105
  recurrence2C0_coeff_106
  recurrence2C0_coeff_107
  recurrence2C0_coeff_108
  recurrence2C0_coeff_109
  recurrence2C0_coeff_110
  recurrence2C0_coeff_111
  recurrence2C0_coeff_112
  recurrence2C0_coeff_113
  recurrence2C0_coeff_114
  recurrence2C0_coeff_115
  recurrence2C0_coeff_116
  recurrence2C0_coeff_117
  recurrence2C0_coeff_118
  recurrence2C0_coeff_119
  recurrence2C0_coeff_120
  recurrence2C0_coeff_121
  recurrence2C0_coeff_122
  recurrence2C0_coeff_123
  recurrence2C0_coeff_124
  recurrence2C0_coeff_125
  recurrence2C0_coeff_126
  recurrence2C0_coeff_127
  recurrence2C0_coeff_128
  recurrence2C0_coeff_129
  recurrence2C0_coeff_130
  recurrence2C0_coeff_131
  recurrence2C0_coeff_132
  recurrence2C0_coeff_133
  recurrence2C0_coeff_134
  recurrence2C0_coeff_135
  recurrence2C0_coeff_136
  recurrence2C0_coeff_137
  recurrence2C0_coeff_138
  recurrence2C0_coeff_139
  recurrence2C0_coeff_140
  recurrence2C0_coeff_141
  recurrence2C0_coeff_142
  recurrence2C0_coeff_143
  recurrence2C0_coeff_144
  recurrence2C0_coeff_145
  recurrence2C0_coeff_146
  recurrence2C0_coeff_147
  recurrence2C0_coeff_148
  recurrence2C0_coeff_149
  recurrence2C0_coeff_150
  recurrence2C0_coeff_151
  recurrence2C0_coeff_152
  recurrence2C0_coeff_153
  recurrence2C0_coeff_154
  recurrence2C0_coeff_155
  recurrence2C0_coeff_156
  recurrence2C0_coeff_157
  recurrence2C0_coeff_158
  recurrence2C0_coeff_159
  recurrence2C0_coeff_160
  recurrence2C0_coeff_161
  recurrence2C0_coeff_162
  recurrence2C0_coeff_163
  recurrence2C0_coeff_164
  recurrence2C0_coeff_165
  recurrence2C0_coeff_166
  recurrence2C0_coeff_167
  recurrence2C0_coeff_168
  recurrence2C0_coeff_169
  recurrence2C0_coeff_170
  recurrence2C0_coeff_171
  recurrence2C0_coeff_172
  recurrence2C0_coeff_173
  recurrence2C0_coeff_174
  recurrence2C0_coeff_175
  recurrence2C0_coeff_176
  recurrence2C0_coeff_177
  recurrence2C0_coeff_178
  recurrence2C0_coeff_179
  recurrence2C0_coeff_180
  recurrence2C0_coeff_181
  recurrence2C0_coeff_182
  recurrence2C0_coeff_183
  recurrence2C0_coeff_184
  recurrence2C0_coeff_185
  recurrence2C0_coeff_186
  recurrence2C0_coeff_187
  recurrence2C0_coeff_188
  recurrence2C0_coeff_189
  recurrence2C0_coeff_190
  recurrence2C0_coeff_191
  recurrence2C0_coeff_192
  recurrence2C0_coeff_193
  recurrence2C0_coeff_194

private theorem recurrence2Scalar0Exceptional_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (313 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_313 :
    recurrence2Scalar0Exceptional.coeff 313 =
      (((40627693261718843912975071827347 * 10 ^ 70 +
        6925712030612436085177424754570902606942647845620071905811840353983843) * 10 ^ 70 +
        5816412160725570566238853981370886299225581141000929759619778227052600) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 119 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 11 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (314 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_314 :
    recurrence2Scalar0Exceptional.coeff 314 =
      (((912069929414519886267276898758 * 10 ^ 70 +
        6425599035673400756747579571386293465879315103986035761652523943735891) * 10 ^ 70 +
        1951638568980240800987248635690442897745821577341171072502756912163100) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 120 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 10 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (315 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_315 :
    recurrence2Scalar0Exceptional.coeff 315 =
      -(((1923728069380584480278129213451 * 10 ^ 70 +
        1017524035404767773146093213827793542726221602067785059080893209905233) * 10 ^ 70 +
        3635740443632282476764176593152394798961633714925996079256958337566852) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 121 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 9 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (316 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_316 :
    recurrence2Scalar0Exceptional.coeff 316 =
      (((478931550550300139503417039955 * 10 ^ 70 +
        0336143846911064208081577800441281891636513951866818274315132519818782) * 10 ^ 70 +
        6867734703114322058124701440461772419806259540685461698079737385035690) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 122 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 8 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (317 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_317 :
    recurrence2Scalar0Exceptional.coeff 317 =
      -(((52369803124807781820871502022 * 10 ^ 70 +
        3328445994576987332310058849504395215615020534264811860162065578795423) * 10 ^ 70 +
        4137653200192052197325743525177610018340132328731338529699409199144053) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 123 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 7 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (318 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_318 :
    recurrence2Scalar0Exceptional.coeff 318 =
      -(((3334807923400619107476865193 * 10 ^ 70 +
        6214970301349103870444231752099090852799585896644353626043812139973328) * 10 ^ 70 +
        9963478314633985642687549409205387971934430687052288523787965106252886) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 124 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 6 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (319 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_319 :
    recurrence2Scalar0Exceptional.coeff 319 =
      (((2309668772067368458780058504 * 10 ^ 70 +
        2525983144265291125271364229058276550105699826676115803423219446112696) * 10 ^ 70 +
        2223477416326517154564677058098291410559794636751184686440008604366271) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 125 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 5 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (320 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_320 :
    recurrence2Scalar0Exceptional.coeff 320 =
      -(((373700876175921726424896981 * 10 ^ 70 +
        5962944936169950568219734705794487223663559980414958822190564800699656) * 10 ^ 70 +
        8887558019269918955664623499946132591702987259682897699861986130813335) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 126 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 4 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (321 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_321 :
    recurrence2Scalar0Exceptional.coeff 321 =
      (((9853191657987538575526719 * 10 ^ 70 +
        0975570030873281712027692064457221033538179748346008751029550872155519) * 10 ^ 70 +
        3744318548826480598698401499394089930842548318064761521390125019240227) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 127 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 3 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (322 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_322 :
    recurrence2Scalar0Exceptional.coeff 322 =
      (((7135991837247487775535645 * 10 ^ 70 +
        3675832825685843417573913083949254009109639030664426463370336996425097) * 10 ^ 70 +
        9898808837758105341189935920177948164879537593119138486441986044709804) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 128 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 2 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (323 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_323 :
    recurrence2Scalar0Exceptional.coeff 323 =
      -(((1241363710467434377197571 * 10 ^ 70 +
        7784004739349815763693185605981096477633345342368577064572490738717256) * 10 ^ 70 +
        5933338103223275684859453257553611664815881561358095327709726080279954) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 129 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 1 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (324 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_324 :
    recurrence2Scalar0Exceptional.coeff 324 =
      (((3283358208682570513380 * 10 ^ 70 +
        1207185388915442528516117949127109257337970353549253483855979370975730) * 10 ^ 70 +
        1470005902667061799868468213154894510991198689848229134761057042929257) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 130 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (325 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_325 :
    recurrence2Scalar0Exceptional.coeff 325 =
      (((25817007487769173157518 * 10 ^ 70 +
        6140707875165777286265907469547174497418997454297419561489499724501334) * 10 ^ 70 +
        5462649952826333543712693794306573604236501372615307775072006196074424) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 131 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 31 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (326 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_326 :
    recurrence2Scalar0Exceptional.coeff 326 =
      -(((2392404810161593292044 * 10 ^ 70 +
        0894499073081361270677690955464079083766875007739352424433055981726812) * 10 ^ 70 +
        2066569105896894214387779129436982141292098386278344167651098632344841) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 132 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 30 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (327 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_327 :
    recurrence2Scalar0Exceptional.coeff 327 =
      -(((444288667555734263878 * 10 ^ 70 +
        2871558134208060097066898698226422084618577009256130552727317254334520) * 10 ^ 70 +
        3136263163180463631343142442329877772999739144151873879042319786000011) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 133 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 29 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (328 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_328 :
    recurrence2Scalar0Exceptional.coeff 328 =
      (((110908266604634067644 * 10 ^ 70 +
        0503550503642397142572279852686106164759257389530356276512790390755849) * 10 ^ 70 +
        2342102469631787899338498057135154196444708692884727931870976022492371) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 134 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 28 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (329 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_329 :
    recurrence2Scalar0Exceptional.coeff 329 =
      -(((602556911900047361 * 10 ^ 70 +
        0282255714498476679286547475888384010346985676792036327817678510755094) * 10 ^ 70 +
        4372206336283598181686423889310553599812688571744673570277415729195248) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 135 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 27 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (330 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_330 :
    recurrence2Scalar0Exceptional.coeff 330 =
      -(((2720805823138029237 * 10 ^ 70 +
        7772154749060233325646639966228964974563900219026599003700222853273395) * 10 ^ 70 +
        8205216201445756759207656879374296282074715768723764064489618213892932) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 136 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 26 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (331 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_331 :
    recurrence2Scalar0Exceptional.coeff 331 =
      (((323680619809591065 * 10 ^ 70 +
        3931077723159643403528193000601948279212969649083999574933519809642576) * 10 ^ 70 +
        8064257313518979415000710077682641579385575341305453737466861592644434) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 137 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 25 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (332 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_332 :
    recurrence2Scalar0Exceptional.coeff 332 =
      (((22257331312666993 * 10 ^ 70 +
        2787882516140613015072613766192526144678904716112806189734475657659924) * 10 ^ 70 +
        9363702252588248086303729686885028843070311304259383927938252580802804) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 138 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 24 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (333 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_333 :
    recurrence2Scalar0Exceptional.coeff 333 =
      -(((8410133343129128 * 10 ^ 70 +
        5225953477390907948291821059493636656944499445243516178385667858346965) * 10 ^ 70 +
        0674181149515824139518263606126366126441149494320750082009427395680782) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 139 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 23 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (334 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_334 :
    recurrence2Scalar0Exceptional.coeff 334 =
      (((379666602022818 * 10 ^ 70 +
        2533901192387312715877974971368232410055558490233502009076034325068263) * 10 ^ 70 +
        2513868574698413766710306377371085477237752067910242973532903942852848) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 140 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 22 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (335 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_335 :
    recurrence2Scalar0Exceptional.coeff 335 =
      (((102000767163571 * 10 ^ 70 +
        9456478166017339203790070117938287197326077758245135234115054065581571) * 10 ^ 70 +
        0556731773939359096926147164035614584002153513058438586935341688159907) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 141 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 21 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (336 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_336 :
    recurrence2Scalar0Exceptional.coeff 336 =
      -(((12834799925145 * 10 ^ 70 +
        3914599178692664024851270682380476871295742588377108310935137290155210) * 10 ^ 70 +
        0204371890718670421450252607956532259475609665299102784337894962850837) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 142 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 20 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (337 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_337 :
    recurrence2Scalar0Exceptional.coeff 337 =
      -(((537291076535 * 10 ^ 70 +
        9775458882066163626040149846493959894531145539194129188139764149764919) * 10 ^ 70 +
        6891568739709302946848727250011543089031391550982202904437157447199836) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 143 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 19 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (338 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_338 :
    recurrence2Scalar0Exceptional.coeff 338 =
      (((182197382754 * 10 ^ 70 +
        9222872208947686728561021782997817937740220939350787466877519166166980) * 10 ^ 70 +
        5720973124680755844217217236981114043873016733970265584346184146698185) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 144 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 18 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (339 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_339 :
    recurrence2Scalar0Exceptional.coeff 339 =
      -(((2056984577 * 10 ^ 70 +
        0023399435709789210727864072131210897884128131958495578355493516783700) * 10 ^ 70 +
        9166037063864421283279543415502691646953469784345946614186177243430811) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 145 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 17 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (340 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_340 :
    recurrence2Scalar0Exceptional.coeff 340 =
      -(((1740775701 * 10 ^ 70 +
        3327354072161394226333227329318130735731557467402815264483594382202583) * 10 ^ 70 +
        8585984249937844098901100299464496005090914571563430246022558219051746) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 146 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 16 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (341 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_341 :
    recurrence2Scalar0Exceptional.coeff 341 =
      (((61821980 * 10 ^ 70 +
        8071475621895784062515512810772288819444413441363921911457754947783725) * 10 ^ 70 +
        8532616897593468898865468094425449264177878258889822910744748230975241) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 147 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 15 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Exceptional_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2ExceptionalProduct.coeff x * remainder4Coefficient0.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2C0_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Exceptional_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2ExceptionalProduct.coeff (194 + x) *
        remainder4Coefficient0.coeff (342 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2ExceptionalProduct_coeff_high (194 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Exceptional_coeff_342 :
    recurrence2Scalar0Exceptional.coeff 342 =
      (((13322817 * 10 ^ 70 +
        4163507305876377393251146344717032595489189080883932720682010334383768) * 10 ^ 70 +
        9557479742931498691171941401776907672198807219306872587362895454345073) : ℚ) := by
  unfold recurrence2Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 148 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 14 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Exceptional_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Exceptional_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
