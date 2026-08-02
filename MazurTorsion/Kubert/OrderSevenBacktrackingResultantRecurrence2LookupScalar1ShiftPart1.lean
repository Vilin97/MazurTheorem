/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB5A6
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Shift coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence2Scalar1Shift_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (235 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_235 :
    recurrence2Scalar1Shift.coeff 235 =
      -((((96 * 10 ^ 70 +
        3484717578812104269677688796001658795728047916189201735102609300962182) * 10 ^ 70 +
        0624966814672203935414241457535320389235703599963284260788586824690207) * 10 ^ 70 +
        9238178499975802403095978784042685746163787830893008156189509631366917) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 6 +
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
    rw [show 102 = 21 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (236 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_236 :
    recurrence2Scalar1Shift.coeff 236 =
      ((((81 * 10 ^ 70 +
        0593393074316921027608406742977787432690065616324887312603043295040860) * 10 ^ 70 +
        9694465376379476607633747701084908484832602856533580989268844550235706) * 10 ^ 70 +
        2518901410816918094993987034972073184113841862659649414262405437785809) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 7 +
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
    rw [show 102 = 20 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (237 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_237 :
    recurrence2Scalar1Shift.coeff 237 =
      -((((58 * 10 ^ 70 +
        9445324609038172165734062486114933271551241843775246114110945267330655) * 10 ^ 70 +
        7816758410685583673428316653032293579718715418696940008241815924677963) * 10 ^ 70 +
        5083469110808353267861979059792007467288098483312874447485120412999243) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 8 +
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
    rw [show 102 = 19 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (238 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_238 :
    recurrence2Scalar1Shift.coeff 238 =
      ((((31 * 10 ^ 70 +
        7922217235146544895569359243360094762683202198149890241321032213258714) * 10 ^ 70 +
        0287480270616432643320415240740536373985036756114390829630288933789988) * 10 ^ 70 +
        5244587599352438982462385796195050374685966038846955364258829636797923) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 9 +
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
    rw [show 102 = 18 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (239 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_239 :
    recurrence2Scalar1Shift.coeff 239 =
      -((((2 * 10 ^ 70 +
        0695734594461655728333251547210832881760623491206342528715614747861517) * 10 ^ 70 +
        2768624055169191550895790212024111289427322607650847797284829259419991) * 10 ^ 70 +
        7164061783079552120555504855361519829856209258914143719124679484980054) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 10 +
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
    rw [show 102 = 17 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (240 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_240 :
    recurrence2Scalar1Shift.coeff 240 =
      -((((27 * 10 ^ 70 +
        4458839357332496031897660012661676778052884549999887214913172184146525) * 10 ^ 70 +
        0148836882616849456620159688196200352506347034573962444341556135808000) * 10 ^ 70 +
        4093855276136399615120933066294141896524402112240124348916770174165591) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 11 +
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
    rw [show 102 = 16 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (241 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_241 :
    recurrence2Scalar1Shift.coeff 241 =
      ((((54 * 10 ^ 70 +
        0826046364469761228375845614326265022960608275144588723128091800853651) * 10 ^ 70 +
        5716084905044629039051172690004304352757779147763905388172416474611946) * 10 ^ 70 +
        7439354821270418096185379269559106055973128326707652796065747569047906) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 12 +
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
    rw [show 102 = 15 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (242 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_242 :
    recurrence2Scalar1Shift.coeff 242 =
      -((((75 * 10 ^ 70 +
        6546017260300816438408643235421168651191666757578856503835542328964914) * 10 ^ 70 +
        3677340879711084132767855658101544235247644694545221512980636722183507) * 10 ^ 70 +
        3657922005882900548105801718627750007739727792516021750202382539364820) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 13 +
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
    rw [show 102 = 14 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (243 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_243 :
    recurrence2Scalar1Shift.coeff 243 =
      ((((90 * 10 ^ 70 +
        7328331397179326858723791984424425968921205970450602064136175116451668) * 10 ^ 70 +
        4859644485329067535918655580677848275409781806051720427825537070342783) * 10 ^ 70 +
        9678908429968798063384981833197235182454336062600415333224833148522817) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 14 +
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
    rw [show 102 = 13 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (244 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_244 :
    recurrence2Scalar1Shift.coeff 244 =
      -((((98 * 10 ^ 70 +
        7663886409124956618101602889040572623480259477815370096579896574053419) * 10 ^ 70 +
        3631987575745932773025146214910989253578360918070027686725060804156281) * 10 ^ 70 +
        8714242632643812707097696265816529212027525017540273855177654562527698) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 15 +
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
    rw [show 102 = 12 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (245 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_245 :
    recurrence2Scalar1Shift.coeff 245 =
      ((((100 * 10 ^ 70 +
        0479092821337045604481531576924234326575997605860019838869876969710606) * 10 ^ 70 +
        6283410947421131253947509177538512290117525592091525344298677757586692) * 10 ^ 70 +
        9802124863332978044168704043598853947028089950182747118491155541357982) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 16 +
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
    rw [show 102 = 11 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (246 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_246 :
    recurrence2Scalar1Shift.coeff 246 =
      -((((95 * 10 ^ 70 +
        5508400332649772155696213632229986093587591476365520221970302621017255) * 10 ^ 70 +
        9882241544468278381984104984056394863821907933996732175271093921736097) * 10 ^ 70 +
        2962326429804302031122375560944583940564148890937831702220382947711549) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 17 +
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
    rw [show 102 = 10 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (247 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_247 :
    recurrence2Scalar1Shift.coeff 247 =
      ((((86 * 10 ^ 70 +
        6880296558643878068335221743657256379567562107312414700497966240259303) * 10 ^ 70 +
        7098130854375262834188042756918581206798069404368260109524148172174232) * 10 ^ 70 +
        9930810831145095518498013386533709664982245078466933415589502339870183) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 18 +
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
    rw [show 102 = 9 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (248 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_248 :
    recurrence2Scalar1Shift.coeff 248 =
      -((((75 * 10 ^ 70 +
        0482325782438218668182786889333316411050948626135008150544441485575826) * 10 ^ 70 +
        1621348849897646343495344707506859845403976000162224443189070552955419) * 10 ^ 70 +
        3383860008620993956456462251144782353476026574166602370018582390334877) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 19 +
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
    rw [show 102 = 8 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (249 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_249 :
    recurrence2Scalar1Shift.coeff 249 =
      ((((62 * 10 ^ 70 +
        1602959383921383861336461839818498537370769721679093896588299561631186) * 10 ^ 70 +
        1193029701578648041191321880879448589991554341728710109553783511697395) * 10 ^ 70 +
        0102337450116657417674384790547293124804674880735622890257176953792098) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 20 +
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
    rw [show 102 = 7 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (250 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_250 :
    recurrence2Scalar1Shift.coeff 250 =
      -((((49 * 10 ^ 70 +
        3187394867180060881898915181432918150818195592919926691974712478305666) * 10 ^ 70 +
        9604900106151726267543615098791889553775610366517378352384202125854975) * 10 ^ 70 +
        7669156666079364162102762190805324767001254886747632439608089805531591) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 21 +
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
    rw [show 102 = 6 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (251 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_251 :
    recurrence2Scalar1Shift.coeff 251 =
      ((((37 * 10 ^ 70 +
        4849712274566393532908473149126204506165711818530949284950040572298253) * 10 ^ 70 +
        0060881903467538844818985425944715352047507682177315378342616295068745) * 10 ^ 70 +
        3982697486533657600635232840946490378604014689898708123929931763822727) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 22 +
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
    rw [show 102 = 5 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (252 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_252 :
    recurrence2Scalar1Shift.coeff 252 =
      -((((27 * 10 ^ 70 +
        2608543573824986935350238714743580108105725628766620259374088062777961) * 10 ^ 70 +
        2434133142987385158135977044301358948862531517374548883121069620709127) * 10 ^ 70 +
        8556453244338287932378100629084683647258566311592473321013681443429384) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 23 +
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
    rw [show 102 = 4 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (253 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_253 :
    recurrence2Scalar1Shift.coeff 253 =
      ((((18 * 10 ^ 70 +
        9191826668835279971140865907071779895331775212850202793069450255199421) * 10 ^ 70 +
        8972001698033672766458783526109244210616359263986217300698162543559978) * 10 ^ 70 +
        8227987707214992767402104454830117459068068941809925886790485078988505) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 24 +
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
    rw [show 102 = 3 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (254 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_254 :
    recurrence2Scalar1Shift.coeff 254 =
      -((((12 * 10 ^ 70 +
        4699804549497340266594540505121408265379902062049368376513098378564657) * 10 ^ 70 +
        9203783388054047402784133893255566240754102713949151826544401135135375) * 10 ^ 70 +
        9038089083951152093593667234406501625164663126704454065265073753629610) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 25 +
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
    rw [show 102 = 2 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (255 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_255 :
    recurrence2Scalar1Shift.coeff 255 =
      ((((7 * 10 ^ 70 +
        7416701833723312772851526657683327060657010669295347584686423185130917) * 10 ^ 70 +
        2722925170666785834614064659894557558546419160351720552829371570982982) * 10 ^ 70 +
        2695309298230283313674519736102659901375928914783307246917144788156277) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 26 +
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
    rw [show 102 = 1 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (256 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_256 :
    recurrence2Scalar1Shift.coeff 256 =
      -((((4 * 10 ^ 70 +
        4601978997947637868876119492065875135115601997553244737897106105750744) * 10 ^ 70 +
        8591141030713793458914776490670085854437179695934064111288533457927303) * 10 ^ 70 +
        6388528602715380279262255030106249358520465224821517069314813812160158) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 27 +
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
  rw [recurrence2Scalar1Shift_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (257 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_257 :
    recurrence2Scalar1Shift.coeff 257 =
      ((((2 * 10 ^ 70 +
        3150554376668383364611119098114497072663961081262620587386738947993460) * 10 ^ 70 +
        8061977863965891950529523453659950965447137752587202220373468919273597) * 10 ^ 70 +
        5256175478780274260965696855259186994151361942013529894845146651665565) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 28 +
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
    rw [show 134 = 31 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (258 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_258 :
    recurrence2Scalar1Shift.coeff 258 =
      -((((1 * 10 ^ 70 +
        0070105323585018599251832832134811064187453614216379673769359880085740) * 10 ^ 70 +
        2099475772432148288662793009489296115843413892695252337703827109956697) * 10 ^ 70 +
        7250233486728409406838640977437675457714857202607384575912254929027760) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 29 +
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
    rw [show 134 = 30 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (259 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_259 :
    recurrence2Scalar1Shift.coeff 259 =
      (((2771039330040028663010828350999171959545563384290667109997646697726799 * 10 ^ 70 +
        3535662453734003999718209245160479318586048812003921566237501235515991) * 10 ^ 70 +
        0422366466767509728058338469394564530804087538709170016137359957223252) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 30 +
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
    rw [show 134 = 29 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (260 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_260 :
    recurrence2Scalar1Shift.coeff 260 =
      (((803978640672244478718633561997806941193423005798021445680149666729001 * 10 ^ 70 +
        5833464275165179048158025002899659707865319298699600948814599416739275) * 10 ^ 70 +
        6812874543742519420071054117452607564481100159676983025888703203022712) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 31 +
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
    rw [show 134 = 28 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (261 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_261 :
    recurrence2Scalar1Shift.coeff 261 =
      -(((2168797692300353286441443357649223643029930910508017631824385178937271 * 10 ^ 70 +
        8341418019492297662804771317697722321703238519060866712727018490709064) * 10 ^ 70 +
        3319317660083569225355664990651994283585571957660154215629112206448090) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 32 +
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
    rw [show 134 = 27 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (262 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_262 :
    recurrence2Scalar1Shift.coeff 262 =
      (((2356271255661626949613909805350819947552262485077708068274027114918018 * 10 ^ 70 +
        5274620525288010827192254927350322773962120717973716668754430583229569) * 10 ^ 70 +
        9540992262190070910247987004058823671918591286191279126266822584443332) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 33 +
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
    rw [show 134 = 26 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (263 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_263 :
    recurrence2Scalar1Shift.coeff 263 =
      -(((2015852154748102692927597152613867166692192962358288235405105400151705 * 10 ^ 70 +
        2593383237713782798681831978951285108742885983738951314637657863377207) * 10 ^ 70 +
        3937458994830197698029209993537125923021482214155759489485686419858573) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 34 +
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
    rw [show 134 = 25 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (264 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_264 :
    recurrence2Scalar1Shift.coeff 264 =
      (((1517757368616306667961140524881346086753429139828956278100249991145740 * 10 ^ 70 +
        5145031675306300839988696224739964826983785509360036364703749529932888) * 10 ^ 70 +
        5303857964754657178950731823742518673349867484119581705877445849604821) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 35 +
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
    rw [show 134 = 24 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (265 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_265 :
    recurrence2Scalar1Shift.coeff 265 =
      -(((1045970409752584959354711391062765139793655640033111940493433450606567 * 10 ^ 70 +
        3345931766415168513998165722627062889880849997410702220420360408493135) * 10 ^ 70 +
        8251925554557820724198637044663617016988618461428493936737214034909845) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 36 +
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
    rw [show 134 = 23 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (266 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_266 :
    recurrence2Scalar1Shift.coeff 266 =
      (((671677192903006990703862282861431206391572846215817712610013104107740 * 10 ^ 70 +
        1376040958435818591915124816817140313349985691923691187729425714607656) * 10 ^ 70 +
        5438488683466812705327192327726234508053215290302118009506094861043963) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 37 +
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
    rw [show 134 = 22 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (267 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_267 :
    recurrence2Scalar1Shift.coeff 267 =
      -(((405526565691597300887807699257210297626836156982414501178738562651509 * 10 ^ 70 +
        8726184432520824535412862268563624531308028653523205802054489285870520) * 10 ^ 70 +
        0690652747275663219556444759452937872806180816841865440920526940191946) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 38 +
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
    rw [show 134 = 21 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (268 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_268 :
    recurrence2Scalar1Shift.coeff 268 =
      (((231209614708397695508392574096532725389462835517176345680283651474162 * 10 ^ 70 +
        2423576599512942986301207938430456534849040097724750334069829599561432) * 10 ^ 70 +
        9246626414778802384048403919306537089564922020921228095833849611574221) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 39 +
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
    rw [show 134 = 20 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (269 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_269 :
    recurrence2Scalar1Shift.coeff 269 =
      -(((124677336927372296389738185977872402273428532287064044578456746174953 * 10 ^ 70 +
        9206614490343414172638554774202809597110280080364752280278678767957162) * 10 ^ 70 +
        1144548667236918759388229304066218017898671574661875471845025306642227) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 40 +
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
    rw [show 134 = 19 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (270 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_270 :
    recurrence2Scalar1Shift.coeff 270 =
      (((63540568069054741453537729907829884221411303867144288110721765321260 * 10 ^ 70 +
        3872467644110942278818597655709309813152670721375178660151664135267853) * 10 ^ 70 +
        9099039622539572947326993188288803641748254949372681127856892513917919) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 41 +
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
    rw [show 134 = 18 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (271 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_271 :
    recurrence2Scalar1Shift.coeff 271 =
      -(((30512359373490884712495700010526138147462158410337684645733911790250 * 10 ^ 70 +
        3865607989584004166778601129722269025866043792422662091994728573037253) * 10 ^ 70 +
        2251067245712333720276954112202728427705238826993514364632652855360007) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 42 +
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
    rw [show 134 = 17 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (272 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_272 :
    recurrence2Scalar1Shift.coeff 272 =
      (((13721390456202815519660695342521741006750101308843212158535044532829 * 10 ^ 70 +
        4151346662330895798231632575727730851361665798192195684789375204900930) * 10 ^ 70 +
        4824064702103572973203162820663678925481456240847308461315865324354505) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 43 +
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
    rw [show 134 = 16 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (273 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_273 :
    recurrence2Scalar1Shift.coeff 273 =
      -(((5713822004223254624501217040335846565020910501290656675915629269526 * 10 ^ 70 +
        3785831643449063620319882624153664794939391817168089688314106599505017) * 10 ^ 70 +
        7126388417508972888284883850275750851739173497462230284107026690609262) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 44 +
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
    rw [show 134 = 15 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (274 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_274 :
    recurrence2Scalar1Shift.coeff 274 =
      (((2156119422815563070196413559933850294356061225812633184868286733347 * 10 ^ 70 +
        0736575741448570495204962552850432814141923211968843524825868760326771) * 10 ^ 70 +
        6902833220363789820692483863481415724473783297570681474554244099147745) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 45 +
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
    rw [show 134 = 14 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (275 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_275 :
    recurrence2Scalar1Shift.coeff 275 =
      -(((702827199570982040351115263182496172197279738607843183284838702078 * 10 ^ 70 +
        4652604591777024410363163122287631765656621163681668789168369801915481) * 10 ^ 70 +
        1802778380766863321014624871362015472602496634340664508998278900971040) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 46 +
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
    rw [show 134 = 13 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (276 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_276 :
    recurrence2Scalar1Shift.coeff 276 =
      (((171291718443498620655562948017770261674798836250458366214819447205 * 10 ^ 70 +
        2156436803851483694495320692767086489875293733806873630766204413764935) * 10 ^ 70 +
        5367932307353306245982229483586011103773883685521306459004609410169815) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 47 +
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
    rw [show 134 = 12 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (277 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_277 :
    recurrence2Scalar1Shift.coeff 277 =
      -(((7879979591678987189230866647486533487280627552213189308256311760 * 10 ^ 70 +
        2646551695814545400592208483922909671606549492657800490222855476450316) * 10 ^ 70 +
        8446082720291376589247934236291817523256952271092918694270407255260235) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 48 +
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
    rw [show 134 = 11 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (278 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_278 :
    recurrence2Scalar1Shift.coeff 278 =
      -(((25861834239707563336932192022707280890474109966015928707067314323 * 10 ^ 70 +
        4220218199553386347076472209542696853479217118394635209969346166302084) * 10 ^ 70 +
        0326255824334397627187668232236223944655939559602485076954645731422684) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 49 +
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
    rw [show 134 = 10 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (279 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_279 :
    recurrence2Scalar1Shift.coeff 279 =
      (((22652879165156714128934673963872216246882895646720835874435595341 * 10 ^ 70 +
        4740860614333034228750606779751466224999576648242635939931089689235710) * 10 ^ 70 +
        5132714268396656869352256607337778029832268943055744118559441997734222) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 50 +
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
    rw [show 134 = 9 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (280 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_280 :
    recurrence2Scalar1Shift.coeff 280 =
      -(((13682539450043850763897772515148932884803772798786435886514596391 * 10 ^ 70 +
        0228189930786963635810394990849318352550824260519875684010749754272021) * 10 ^ 70 +
        2622492362057547356740503914470401893796105334095891910537854919553188) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 51 +
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
    rw [show 134 = 8 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (281 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_281 :
    recurrence2Scalar1Shift.coeff 281 =
      (((6967954565888100588610579039726702172960823878367495814008659309 * 10 ^ 70 +
        9233889998666413314471825301698610499040472812391781497651298591752170) * 10 ^ 70 +
        3092785321413473131953193303920924032348805892978851475659494785284599) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 52 +
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
    rw [show 134 = 7 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (282 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_282 :
    recurrence2Scalar1Shift.coeff 282 =
      -(((3168716760185498241515553388343030309629745595335900325787998651 * 10 ^ 70 +
        3032767422105186965200147784466941584658154056598500734335322083396488) * 10 ^ 70 +
        5281338328190971746777758609339858785796887682477991601975737454726505) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 53 +
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
    rw [show 134 = 6 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (283 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_283 :
    recurrence2Scalar1Shift.coeff 283 =
      (((1316782144576679298502118518545355442648961817252041725907663882 * 10 ^ 70 +
        9377654041952346433521961284556693154147595811362889192507508015793080) * 10 ^ 70 +
        0424704846158179636877149755934244118159687355460209610506764728529304) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 54 +
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
    rw [show 134 = 5 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (284 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_284 :
    recurrence2Scalar1Shift.coeff 284 =
      -(((504977185590441335944326136892877837828402534085847410800046283 * 10 ^ 70 +
        1952932565694308412968374140057752397263892932978153523442846017100159) * 10 ^ 70 +
        0163073999876288373230585004433808576759732444099405071564047573683029) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 55 +
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
    rw [show 134 = 4 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (285 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_285 :
    recurrence2Scalar1Shift.coeff 285 =
      (((179211680144764571990302229892211529737658466732405746736179129 * 10 ^ 70 +
        8974506728823913922094378614067497485061159840438481701204441466174118) * 10 ^ 70 +
        4056581473744719856082751141618711863770749715820783108750497356114456) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 56 +
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
    rw [show 134 = 3 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (286 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_286 :
    recurrence2Scalar1Shift.coeff 286 =
      -(((58700955200837572687357175069080134666783873944791645441857795 * 10 ^ 70 +
        5690406269446762091543805998919664487359355487452673023918675963599676) * 10 ^ 70 +
        0888903278082898867454995216684640984442884849686652327016839556113967) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 57 +
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
    rw [show 134 = 2 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (287 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_287 :
    recurrence2Scalar1Shift.coeff 287 =
      (((17586683812243179494852271569303935292925900073166492440435478 * 10 ^ 70 +
        6660032870011689014820457150992922393326552781641571837124532576623974) * 10 ^ 70 +
        9739706872657992066398905586401819428104395944010304167020058993795520) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 58 +
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
    rw [show 134 = 1 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (288 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_288 :
    recurrence2Scalar1Shift.coeff 288 =
      -(((4723796875118752599851920087319073500559141203160204763506795 * 10 ^ 70 +
        4385333522412598014646031103971630023093318716175356074278900120217713) * 10 ^ 70 +
        5670464815325721080571924093123397588569294173834305994710449388788273) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 59 +
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
  rw [recurrence2Scalar1Shift_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (289 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_289 :
    recurrence2Scalar1Shift.coeff 289 =
      (((1086206392675364233917833435315625066827011858518430360902488 * 10 ^ 70 +
        7897986770448557186994906482376439564754337346910458719451644508615476) * 10 ^ 70 +
        4594153383153399840149089001364343430852708387371118640842936455821157) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 60 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 31 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (290 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_290 :
    recurrence2Scalar1Shift.coeff 290 =
      -(((185929863879603446618528084926935623995007294695814804351340 * 10 ^ 70 +
        8896673001657207470376452205065890553806717844711644807077913854578182) * 10 ^ 70 +
        8656243627213803051375234224303860336206525288108782936480950130795700) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 61 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 30 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (291 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_291 :
    recurrence2Scalar1Shift.coeff 291 =
      (((6883734185110712635312238796630489272016331801975575726520 * 10 ^ 70 +
        9793870923031484937935582939005329022040290975312827370720825177551034) * 10 ^ 70 +
        4403354418563807217410349869463449621547106588843426303960435204312659) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 62 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 29 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (292 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_292 :
    recurrence2Scalar1Shift.coeff 292 =
      (((12602309472123284633076761148364386413372351591474220858991 * 10 ^ 70 +
        3892073976646812454138737510610329397331466090797652549778709621011827) * 10 ^ 70 +
        8574899589359934766750984466643991768200896875486129368023073049101646) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 63 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 28 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (293 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_293 :
    recurrence2Scalar1Shift.coeff 293 =
      -(((7543541552960669811300868898538804533323039139223585972887 * 10 ^ 70 +
        9530487145349553207991959975483440369678251468880178058068877876382690) * 10 ^ 70 +
        6685475584034288729876686451961407285537905630925366319510764537292612) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 64 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 27 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (294 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_294 :
    recurrence2Scalar1Shift.coeff 294 =
      (((3048241205596850088893984472250331437691159753944869777781 * 10 ^ 70 +
        7325169384542393362480810401981414155860542986031354552419278881873947) * 10 ^ 70 +
        6683582980815004100671808098540641523825644751831156317212236582416165) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 65 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 26 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (295 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_295 :
    recurrence2Scalar1Shift.coeff 295 =
      -(((1022722727578770406581421676556586244353856717911078115954 * 10 ^ 70 +
        6718699389119651741142991963934808881089208558911614245451226827326905) * 10 ^ 70 +
        6080961658380355286336643918902015361663074700913514346945524542663249) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 66 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 25 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (296 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_296 :
    recurrence2Scalar1Shift.coeff 296 =
      (((301517300180558826803805655997051310757950133599997422834 * 10 ^ 70 +
        5739965599147482542100018895812602069854107068180491265457463736181051) * 10 ^ 70 +
        8809557592828492649093928650449356653276949173378248817619185146598097) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 67 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 24 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (297 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_297 :
    recurrence2Scalar1Shift.coeff 297 =
      -(((79706951347969051011384953452592231658179810534960365475 * 10 ^ 70 +
        5762670302714500188088618316778700886060433018690118067280318189700044) * 10 ^ 70 +
        8467580206847576524201232159779117654380478649423194208798254025370481) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 68 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 23 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (298 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_298 :
    recurrence2Scalar1Shift.coeff 298 =
      (((18981136902821035201044958348615683360388957920191597854 * 10 ^ 70 +
        2636959799105807159861422139643478357453093071713590127181368341343202) * 10 ^ 70 +
        2858475015015944626391273790799219972765981328879382112979648178544891) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 69 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 22 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (299 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_299 :
    recurrence2Scalar1Shift.coeff 299 =
      -(((4043946410353767732617124652638535696219353770500096055 * 10 ^ 70 +
        7400449971241500318513255875934914123631862045948221686521180893126620) * 10 ^ 70 +
        8725886206706160086310039665383721902059684801239412438025670216524663) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 70 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 21 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (300 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_300 :
    recurrence2Scalar1Shift.coeff 300 =
      (((753507954258826659250446732513978313219804736085205487 * 10 ^ 70 +
        5964136474536411076095729670308561253296612516635826050603334283007037) * 10 ^ 70 +
        4594265911692470886501625784025220999967231458516225079219463538764596) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 71 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 20 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (301 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_301 :
    recurrence2Scalar1Shift.coeff 301 =
      -(((115632063425447496360648786655416323027078531288474573 * 10 ^ 70 +
        2886533319015437262977853588440241540753287528471796705975148933504294) * 10 ^ 70 +
        2114023324881930264790169756006415871592278326419740921121667788320792) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 72 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 19 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (302 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_302 :
    recurrence2Scalar1Shift.coeff 302 =
      (((11768614193698311528134403182438696648358821370790966 * 10 ^ 70 +
        4770417993940612768324519981365764337527632920939574380700894415198094) * 10 ^ 70 +
        6106765592307693956030765044488659624065805667657992066274386234585626) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 73 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 18 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (303 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_303 :
    recurrence2Scalar1Shift.coeff 303 =
      (((465107340803703962570563186731469919100574370406288 * 10 ^ 70 +
        2805079594533635465507429060330563706477462558424602603436048115114193) * 10 ^ 70 +
        6344323988483337900545811990086698458323777873783562830369135983768533) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 74 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 17 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (304 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_304 :
    recurrence2Scalar1Shift.coeff 304 =
      -(((668042274050664535972283290080237798786147296656085 * 10 ^ 70 +
        5747514629319695963330959843330630666092025102960386594543959600756446) * 10 ^ 70 +
        1525709074749550721670437304598977122325687262542087434409054231354008) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 75 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 16 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (305 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_305 :
    recurrence2Scalar1Shift.coeff 305 =
      (((229485106711896216183207230144105176496357581387539 * 10 ^ 70 +
        1713264333560305676488027034235463898650141253482771221258244268882433) * 10 ^ 70 +
        7763367800475283362755847009203923826554690129789069672081546376463812) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 76 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 15 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (306 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_306 :
    recurrence2Scalar1Shift.coeff 306 =
      -(((57831479255666939235005363757725957567855487078439 * 10 ^ 70 +
        2253738984155829449509733300577851303607790742297620581205692427551402) * 10 ^ 70 +
        9957260764275471689303067790060909130189504914786708838890368610288565) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 77 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 14 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (307 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_307 :
    recurrence2Scalar1Shift.coeff 307 =
      (((12186347333044047729412995292842714970865600445245 * 10 ^ 70 +
        9490268038839200078288661343960865541509757291236841389776114320501032) * 10 ^ 70 +
        7039871288385634902408644249949946070512386144314412815855707232465487) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 78 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 13 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (308 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_308 :
    recurrence2Scalar1Shift.coeff 308 =
      -(((2231013517870218208436648741647452838816585225910 * 10 ^ 70 +
        9693553401855903926995899555681157624773765208192601553816860316308801) * 10 ^ 70 +
        3071916941543320843894425994327188385912127043354919460002713991808227) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 79 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 12 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (309 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_309 :
    recurrence2Scalar1Shift.coeff 309 =
      (((357875636814139279111330973776649441186752110910 * 10 ^ 70 +
        3636048190404150051902073441047475668533926645954519623137957404841847) * 10 ^ 70 +
        5139699151394950019287615750819412905619226035780215506900743732754594) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 80 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 11 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (310 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_310 :
    recurrence2Scalar1Shift.coeff 310 =
      -(((49708368549198023253243552112830073223183831162 * 10 ^ 70 +
        3551646349111922686402490372547626837156462731793072749629810889039100) * 10 ^ 70 +
        3588218813418715662511716037019667926488466722705003809306621005875646) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 81 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 10 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (311 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_311 :
    recurrence2Scalar1Shift.coeff 311 =
      (((5719958320353379572832362104056911457819354838 * 10 ^ 70 +
        4170865509269368021097514658327691885472177826510492976469460849199957) * 10 ^ 70 +
        7732074637414897178819147535692099993599521975255988157742928911003889) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 82 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 9 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (312 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_312 :
    recurrence2Scalar1Shift.coeff 312 =
      -(((467954262427806790775108091483839505744843276 * 10 ^ 70 +
        3351182241226921170997561062270667730126265309335730083668499039967528) * 10 ^ 70 +
        1540010383055051807720765087094718648846744198223739454606978364590683) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 83 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 8 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (313 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_313 :
    recurrence2Scalar1Shift.coeff 313 =
      (((3693387992360813562468793253713422383847100 * 10 ^ 70 +
        4521323087889814335394713440466227636635130635133380292762054584920183) * 10 ^ 70 +
        2879089806502897534865617704442804819568882812679751863520847331085467) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 84 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 7 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (314 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_314 :
    recurrence2Scalar1Shift.coeff 314 =
      (((8623399172883070306665617037414461484170725 * 10 ^ 70 +
        3129780912644575180342862174242501127043710344714122948051323673622796) * 10 ^ 70 +
        7486675361560932254887022068716983398123946702530766289775558445956070) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 85 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 6 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (315 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_315 :
    recurrence2Scalar1Shift.coeff 315 =
      -(((2296511777754335313980700361492590470566869 * 10 ^ 70 +
        4916696286587129413519275637971607454087150835614796147308408220964156) * 10 ^ 70 +
        5138520141784576847983709003572974872373928835461813804752165056717550) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 86 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 5 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (316 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_316 :
    recurrence2Scalar1Shift.coeff 316 =
      (((417484896367157600536149970914955346791181 * 10 ^ 70 +
        5380350995584689758395284819927467122111806047640406658522759763259156) * 10 ^ 70 +
        6312790417505149927176933567052948787880578461040821112519873162762848) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 87 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 4 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (317 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_317 :
    recurrence2Scalar1Shift.coeff 317 =
      -(((61790203652997031733362963593319708936715 * 10 ^ 70 +
        7993563452780448004024636930913552891978010111078595211139029794082893) * 10 ^ 70 +
        2365796985286768374694028628104342605024753083626785155084292175976270) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 88 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 3 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (318 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_318 :
    recurrence2Scalar1Shift.coeff 318 =
      (((7746139565487694409938008089488164996520 * 10 ^ 70 +
        9732553142790287899644664038217209223962512259654522921611730702202785) * 10 ^ 70 +
        1699019923358098310954982860790090213000551823730050050840526964632703) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 89 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 2 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (319 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_319 :
    recurrence2Scalar1Shift.coeff 319 =
      -(((815378370273035771260446925960952896613 * 10 ^ 70 +
        3151649160160215437204987729895423662315872889805709387805732376842980) * 10 ^ 70 +
        3285592021720524836294243417290243678879255955273567731526153245642184) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 90 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 1 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (320 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_320 :
    recurrence2Scalar1Shift.coeff 320 =
      (((67443192159925559473018396579858869656 * 10 ^ 70 +
        9810031142701004266396408077090874414326583585329014136550025228773937) * 10 ^ 70 +
        7600625895470180462893483761029284293678519130383704283675846279284098) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 91 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (321 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_321 :
    recurrence2Scalar1Shift.coeff 321 =
      -(((3270316914798826100324063961242514315 * 10 ^ 70 +
        3173373569650814152721186581118148536423199172343026983122596174686367) * 10 ^ 70 +
        9085222449157167965460270125835755791221241027046800971115200935543909) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 92 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 31 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (322 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_322 :
    recurrence2Scalar1Shift.coeff 322 =
      -(((176637564910902261462747712165350681 * 10 ^ 70 +
        4855004513400743469843763011357015152232273780875110906941846799665894) * 10 ^ 70 +
        4600883418067725492740117822072652627620170679811055344635767350628498) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 93 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 30 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (323 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_323 :
    recurrence2Scalar1Shift.coeff 323 =
      (((70192419085263582624498532813299296 * 10 ^ 70 +
        0528892017648337205903534069317617194026104757504218875843172054515437) * 10 ^ 70 +
        0445056065765345912660845778357863651986318790253273043123696338487011) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 94 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 29 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (324 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_324 :
    recurrence2Scalar1Shift.coeff 324 =
      -(((10668373544098375899839625656439698 * 10 ^ 70 +
        3748578686582470020943038909080209360642546689468407585036620560098500) * 10 ^ 70 +
        3791681502553438878559826421605416307911448776914140447122160382825099) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 95 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 28 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (325 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_325 :
    recurrence2Scalar1Shift.coeff 325 =
      (((1124099440754796484211895843248484 * 10 ^ 70 +
        3145186923045093450162397495592325732149798060046500916171498726540627) * 10 ^ 70 +
        7183036627962256754544872362612981890058105267918308992307286637901659) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 96 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 27 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (326 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_326 :
    recurrence2Scalar1Shift.coeff 326 =
      -(((84807941045910271828643130188580 * 10 ^ 70 +
        6997442848196178181194613000994634333625124719026651588895714691748090) * 10 ^ 70 +
        8654366146087414680142429314820698877044804079178897266465875325459574) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 97 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 26 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (327 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_327 :
    recurrence2Scalar1Shift.coeff 327 =
      (((3652235426064342630889491040344 * 10 ^ 70 +
        6254768468980151458278721301710405161803118140889917651202415076262731) * 10 ^ 70 +
        9114670958428618101421933453764961453656089057681590712536241284525992) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 98 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 25 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (328 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_328 :
    recurrence2Scalar1Shift.coeff 328 =
      (((107245001096026958790168525312 * 10 ^ 70 +
        4033352335774025712832240464065391861125830842629161429604675751143094) * 10 ^ 70 +
        5546390617823753811840913670370310144861620372282709974051991357035249) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 99 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 24 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (329 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_329 :
    recurrence2Scalar1Shift.coeff 329 =
      -(((38340820613786692340555054653 * 10 ^ 70 +
        1822740587308531354607225122318769030726035419902126112772787125702947) * 10 ^ 70 +
        4335885006247583375290560301992945360731280949166144750939430727661747) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 100 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 23 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (330 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_330 :
    recurrence2Scalar1Shift.coeff 330 =
      (((4077576829086977074039337868 * 10 ^ 70 +
        5940482206411529704506613902918031342858757107208225460955932481717767) * 10 ^ 70 +
        1907824327997637541973312154413123860976466765111962960125676469878513) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 101 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 22 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (331 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_331 :
    recurrence2Scalar1Shift.coeff 331 =
      -(((261715132600132464168060674 * 10 ^ 70 +
        4151548966727466985025715864836136592878315845281721893913216372027634) * 10 ^ 70 +
        4798334553046371915007964221379997093851842435760915139148964765494961) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 102 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 21 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (332 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_332 :
    recurrence2Scalar1Shift.coeff 332 =
      (((8285367335533400125936941 * 10 ^ 70 +
        1533578037788334904835009525186835867828054175521245178543472032100657) * 10 ^ 70 +
        0952205097361456256133662578375177235353658164284754727234564537265021) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 103 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 20 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (333 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_333 :
    recurrence2Scalar1Shift.coeff 333 =
      (((307374615118008732208087 * 10 ^ 70 +
        4372991205223182088101881331844023804279528277374360078665480328573982) * 10 ^ 70 +
        9300541454639394191895087756420622117603173794583348389729596987263808) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 104 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 19 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (334 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_334 :
    recurrence2Scalar1Shift.coeff 334 =
      -(((60482698547547812167595 * 10 ^ 70 +
        0785284221051345267275573694944245001251911635112581898037496494698212) * 10 ^ 70 +
        1557300439577039334387977420256405648145108558876361664047900375664748) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 105 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 18 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (335 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_335 :
    recurrence2Scalar1Shift.coeff 335 =
      (((4171151555955676068130 * 10 ^ 70 +
        5779484007426587195035775599101868922406275293492772392467707840452325) * 10 ^ 70 +
        4616945133163877179288857908369423881873509440449584648958503633012950) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 106 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 17 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (336 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_336 :
    recurrence2Scalar1Shift.coeff 336 =
      -(((153957333692994430399 * 10 ^ 70 +
        9676745134332467131472618892428528941226844581074537043148201209740633) * 10 ^ 70 +
        1446262837112486530603910948738987046412120254687224609974819723766745) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 198 = 16 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (337 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_337 :
    recurrence2Scalar1Shift.coeff 337 =
      (((769262980239311452 * 10 ^ 70 +
        6670431708365824834546522091183700736199014641367371851870390422001410) * 10 ^ 70 +
        7989267505623692037406308975457754363275001526536423383595102616148194) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 198 = 15 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (338 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_338 :
    recurrence2Scalar1Shift.coeff 338 =
      (((269048024432136180 * 10 ^ 70 +
        6583082660232948139462695234429341518043758627240192882926951579102682) * 10 ^ 70 +
        6985897427098523241715196548465838024978181782076635131530461820164302) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 198 = 14 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (339 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_339 :
    recurrence2Scalar1Shift.coeff 339 =
      -(((16866125152116142 * 10 ^ 70 +
        9683497052977959773253181942828297137746640013362930304847842381487551) * 10 ^ 70 +
        2817086919675934780948365497727074355779421968153995506290383061166637) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 198 = 13 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (340 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_340 :
    recurrence2Scalar1Shift.coeff 340 =
      (((482156108910704 * 10 ^ 70 +
        8165048589111055125124008573380449861774863732362649637735573162746701) * 10 ^ 70 +
        1564435793977507975141988700604588667002344221967672918188992424378159) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 198 = 12 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (341 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_341 :
    recurrence2Scalar1Shift.coeff 341 =
      -(((2251466810938 * 10 ^ 70 +
        0428611007815924796895273185192742098220971201313452682552509233265018) * 10 ^ 70 +
        5673004308403452443682403353408905374035652569542425958837005740755458) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 198 = 11 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (342 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_342 :
    recurrence2Scalar1Shift.coeff 342 =
      -(((356677035091 * 10 ^ 70 +
        3679047804760357409428227392918422767589863854979445929390684262993796) * 10 ^ 70 +
        1146466911598224765013827694802754397982859499935346310275623475926109) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 198 = 10 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (343 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_343 :
    recurrence2Scalar1Shift.coeff 343 =
      (((13547820471 * 10 ^ 70 +
        7316693191835205197325473353817279650161139523074865746130564798129336) * 10 ^ 70 +
        3513814035338899032077895594999978065043713806143223346176887807399261) : ℚ) := by
  unfold recurrence2Scalar1Shift
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
    rw [show 198 = 9 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (344 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_344 :
    recurrence2Scalar1Shift.coeff 344 =
      -(((179569143 * 10 ^ 70 +
        3173593376308425053197375554586639614401408933532306127922230829277761) * 10 ^ 70 +
        6406561874302069445889866544832602400030487847986859721352203448241924) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 115 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 8 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (345 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_345 :
    recurrence2Scalar1Shift.coeff 345 =
      -(((1708535 * 10 ^ 70 +
        1743522740883014070913567075488058175347889302808445697420056413037661) * 10 ^ 70 +
        1324215931882979547090228930881597003100521933999054924765167078766131) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 116 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 7 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (346 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_346 :
    recurrence2Scalar1Shift.coeff 346 =
      (((92444 * 10 ^ 70 +
        6669534726633547829850470866495659734920542887191534925919166949037140) * 10 ^ 70 +
        9184945980906752289745131304256416485697338113829949905019343523703264) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 117 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 6 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (347 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_347 :
    recurrence2Scalar1Shift.coeff 347 =
      -(((990 * 10 ^ 70 +
        2066509625702748765708311092496981512300474443960105483787329325278246) * 10 ^ 70 +
        3444398744317570228554529951234224872874154269893117560265883242148180) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 118 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 5 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (348 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_348 :
    recurrence2Scalar1Shift.coeff 348 =
      -(((5 * 10 ^ 70 +
        5242634405650158448748017937691377566969271432871242994077996758122811) * 10 ^ 70 +
        9722416758391216742991487705441055703735258407952351217796538015556345) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 119 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 4 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (349 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_349 :
    recurrence2Scalar1Shift.coeff 349 =
      ((1916439582804041872507907060249973275028772091291694956978085438104714 * 10 ^ 70 +
        4363352567553237593224661360188406543189070745709218943220728783027080) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 120 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 3 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (350 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_350 :
    recurrence2Scalar1Shift.coeff 350 =
      -((7258288941569823104429136929581691237668776771902019673167427507687 * 10 ^ 70 +
        5729302101774980314407122125952644722030429944185661105584690817676300) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 121 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 2 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (351 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_351 :
    recurrence2Scalar1Shift.coeff 351 =
      -((123280384993621711288762244692711051902388581468071630272932776955 * 10 ^ 70 +
        2809922305793172153223614163350625582223605322574063103142661967946801) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 122 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 1 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (352 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_352 :
    recurrence2Scalar1Shift.coeff 352 =
      ((951168892397358558758716363206423832467134757033378854335661897 * 10 ^ 70 +
        8880753663912525961259307218444506191474101790711845250114101220120436) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 123 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (353 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_353 :
    recurrence2Scalar1Shift.coeff 353 =
      ((3467629762002353561443122587079327958431555063401258111511686 * 10 ^ 70 +
        3809384068241754510296866048624743385272507032044200600099195996809594) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 124 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 31 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (354 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_354 :
    recurrence2Scalar1Shift.coeff 354 =
      -((45349067005314714322359656823785546087004198249592269570456 * 10 ^ 70 +
        1069581225714825634508458417130295731099765253232934288135825856554663) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 125 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 30 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (355 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_355 :
    recurrence2Scalar1Shift.coeff 355 =
      -((26097969624679803860543307695089476148297768889600281031 * 10 ^ 70 +
        0186482823539842039138437843868256020379175291193845936229721524789348) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 126 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 29 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (356 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_356 :
    recurrence2Scalar1Shift.coeff 356 =
      ((1131388678700372124052737313280042735214179809708032046 * 10 ^ 70 +
        5281662394943847120837840835591870650720284269067216207624116852678689) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 127 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 28 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (357 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_357 :
    recurrence2Scalar1Shift.coeff 357 =
      -((982542722637315907089102478021536984614513090698500 * 10 ^ 70 +
        8637949377823524159316720746229199300357714483444306213238577247218368) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 128 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 27 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (358 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_358 :
    recurrence2Scalar1Shift.coeff 358 =
      -((15547062724423495378782920342959903681011896791291 * 10 ^ 70 +
        3103470134695179590103488813640570480851764393745914137484766151217236) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 129 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 26 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (359 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_359 :
    recurrence2Scalar1Shift.coeff 359 =
      ((29613538457672325996471272342638017130582372956 * 10 ^ 70 +
        9127014118870628379682414071307624750315954246899169709396342393479351) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 130 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 25 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (360 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_360 :
    recurrence2Scalar1Shift.coeff 360 =
      ((106982705301376935468094419388446830910647276 * 10 ^ 70 +
        3432774217401311833111862561469521179485389123948762268546426932553265) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 131 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 24 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (361 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_361 :
    recurrence2Scalar1Shift.coeff 361 =
      -((336720367803295822608178644346700730549158 * 10 ^ 70 +
        5879106383819782913656553638407334088500526024213892065588883284097645) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 132 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 23 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (362 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_362 :
    recurrence2Scalar1Shift.coeff 362 =
      -((184327924866978663682147130818675925217 * 10 ^ 70 +
        6442599354119733223133615192100024356981891397847782676740531053635691) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 133 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 22 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (363 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_363 :
    recurrence2Scalar1Shift.coeff 363 =
      ((1637124497575280288357994529924489822 * 10 ^ 70 +
        8872089643986686717164560907081603185764886812058332119006933932017982) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 134 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 21 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (364 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_364 :
    recurrence2Scalar1Shift.coeff 364 =
      -((1434158984376313720315010517494169 * 10 ^ 70 +
        1601658158825684142173095408596128699018916608350860877895569431256498) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 135 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 20 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (365 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_365 :
    recurrence2Scalar1Shift.coeff 365 =
      -((1905295551668522094867155611078 * 10 ^ 70 +
        0657565929298310819865309143527959092393635108341642520098275737214001) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 136 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 19 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (366 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_366 :
    recurrence2Scalar1Shift.coeff 366 =
      ((4303054418452796514757305006 * 10 ^ 70 +
        8538117826378881921255579611320810185757450113311148179258291119860124) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 137 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 18 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (367 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_367 :
    recurrence2Scalar1Shift.coeff 367 =
      -((2617093558235847539819486 * 10 ^ 70 +
        4239009338799570592344638457461055897488761109931109780247434538351467) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 138 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 17 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (368 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_368 :
    recurrence2Scalar1Shift.coeff 368 =
      ((21410664907156726302 * 10 ^ 70 +
        0132190291438455220513080607121445611773376103587469621689132071372722) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 139 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 16 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (369 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_369 :
    recurrence2Scalar1Shift.coeff 369 =
      ((601275027250547330 * 10 ^ 70 +
        3935430784215275429574416090328544096456236918420282048691376629590324) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 140 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 15 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (370 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_370 :
    recurrence2Scalar1Shift.coeff 370 =
      -((237556003902084 * 10 ^ 70 +
        5222624684785817797678869863860761127955146080635713093293766456236739) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 141 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 14 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (371 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_371 :
    recurrence2Scalar1Shift.coeff 371 =
      ((32411342942 * 10 ^ 70 +
        6129005497628942927412559044635481475161936312002721236952992559160306) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 142 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 13 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (372 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_372 :
    recurrence2Scalar1Shift.coeff 372 =
      -((666421 * 10 ^ 70 +
        9067112409026817356407962596311646849614520723125563865679367303092943) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 143 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 12 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (373 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_373 :
    recurrence2Scalar1Shift.coeff 373 =
      -((163 * 10 ^ 70 +
        8247426752605123269079746683954617437412558333969026391882408662628674) : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 144 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 11 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (374 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_374 :
    recurrence2Scalar1Shift.coeff 374 =
      (105175662714001782261935149484042874977134648584263254546421996061775 : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 145 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 10 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (375 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_375 :
    recurrence2Scalar1Shift.coeff 375 =
      (-1878369461119149595505357420861111799888220854844044514029306268 : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 146 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 9 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (376 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_376 :
    recurrence2Scalar1Shift.coeff 376 =
      (8379617675549280037784306732183268668629035211673311546995 : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 147 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 8 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (377 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_377 :
    recurrence2Scalar1Shift.coeff 377 =
      (19516506400240705591384137467204049919784225072076051 : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 148 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 7 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (378 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_378 :
    recurrence2Scalar1Shift.coeff 378 =
      (-91779007694975403946065398805950810314968314574 : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 379 = 149 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 6 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (379 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_379 :
    recurrence2Scalar1Shift.coeff 379 =
      (60951273568382323836751524600664864680464 : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 380 = 150 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 5 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Shift_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient0.coeff x * recurrence2B5A6.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B5A6_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Shift_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient0.coeff (155 + x) *
        recurrence2B5A6.coeff (380 - (155 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B0_coeff_high (155 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Shift_coeff_380 :
    recurrence2Scalar1Shift.coeff 380 =
      (-3360009522262143161703435836062336 : ℚ) := by
  unfold recurrence2Scalar1Shift
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 381 = 151 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 4 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Shift_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Shift_coeff_380_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
