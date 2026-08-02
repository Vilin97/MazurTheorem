/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence2Scalar2Main_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (234 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_234 :
    recurrence2Scalar2Main.coeff 234 =
      ((((848 * 10 ^ 70 +
        4773022010588484361559476895642063200877512033482454834624789450660243) * 10 ^ 70 +
        3980610027480138363451804852857734898309822869658120302479649914689957) * 10 ^ 70 +
        6137770620972292062223135122771781416215814778309433411076376817788609) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 18 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (235 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_235 :
    recurrence2Scalar2Main.coeff 235 =
      -((((894 * 10 ^ 70 +
        2932955438479461812464416941644358325955887551194791927392205296605121) * 10 ^ 70 +
        5891901176252168735344978921865112348331109266796143469638070397389891) * 10 ^ 70 +
        8909162685734654876766258538957881372188839571217572477269133638296718) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 17 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (236 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_236 :
    recurrence2Scalar2Main.coeff 236 =
      ((((890 * 10 ^ 70 +
        8116685136837117251996888341398661737392320267414691550946834444810835) * 10 ^ 70 +
        8519298357711285373346802622894035795414091830908973262193715471434005) * 10 ^ 70 +
        9131472691343777705050546924765223060315783302905269847733257045137863) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 16 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (237 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_237 :
    recurrence2Scalar2Main.coeff 237 =
      -((((834 * 10 ^ 70 +
        7194662067245812222183029049792595035711781949488364125203113763714950) * 10 ^ 70 +
        0795588648328009477155071646348216022247247218859863377722258873549890) * 10 ^ 70 +
        7525161790988804380106319176294977902089550532581351317964596485493089) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 15 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (238 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_238 :
    recurrence2Scalar2Main.coeff 238 =
      ((((729 * 10 ^ 70 +
        3475843244422149673789268150053972175009372419241239136374576663887111) * 10 ^ 70 +
        5844888944886418665208591101163904085342861265374867098319956842786231) * 10 ^ 70 +
        0856844074012681994156903109581811135780259022324470609115782020622517) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 14 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (239 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_239 :
    recurrence2Scalar2Main.coeff 239 =
      -((((584 * 10 ^ 70 +
        3914273660069439537426689419887680819866862335891101403063325916091813) * 10 ^ 70 +
        6773811847236645624867626189187935241442531486212293562748669809631063) * 10 ^ 70 +
        3350756797902992801518438215549406380725205935658640718766283901098559) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 13 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (240 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_240 :
    recurrence2Scalar2Main.coeff 240 =
      ((((414 * 10 ^ 70 +
        4466359732632024816433149848921705441430949007230152176225432239456291) * 10 ^ 70 +
        1491000863762169820104196352792419273365765420366843141213931468215169) * 10 ^ 70 +
        0052267393963592573221164605117450650780702648118502398746315457621190) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 12 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (241 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_241 :
    recurrence2Scalar2Main.coeff 241 =
      -((((236 * 10 ^ 70 +
        6647527704116497269545244914497817093910680147900631031849901826534382) * 10 ^ 70 +
        0224475802388351267858388255825612907215249508586833329202986965346452) * 10 ^ 70 +
        5362073643722140448828723572795411509647045770553863057143649117907273) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 11 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (242 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_242 :
    recurrence2Scalar2Main.coeff 242 =
      ((((68 * 10 ^ 70 +
        0356961850168833889317117942407003855116672244251021866066524961333903) * 10 ^ 70 +
        5764884070327361586034390654081852493121577271220067182346961415654884) * 10 ^ 70 +
        9848928825617028177462179390500136902958205364231190986560300270306380) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 10 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (243 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_243 :
    recurrence2Scalar2Main.coeff 243 =
      ((((77 * 10 ^ 70 +
        1300256438069547055988155747018988191530164668649454564082067644474642) * 10 ^ 70 +
        5996394179637184653215803747320440016775255851756340774495508212708632) * 10 ^ 70 +
        3656130478926561303310007669517068876573656437162454608560006343359756) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 9 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (244 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_244 :
    recurrence2Scalar2Main.coeff 244 =
      -((((189 * 10 ^ 70 +
        0288684067300502468095233406349625666704990916449820900694090291354857) * 10 ^ 70 +
        9467720573478691315232211276580798454695739887098855699424321159576802) * 10 ^ 70 +
        6335863050830441549085216115313735958246858279825245198344006951608574) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 8 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (245 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_245 :
    recurrence2Scalar2Main.coeff 245 =
      ((((263 * 10 ^ 70 +
        2094085682021266442490213830312427364849037740734172524688534622581768) * 10 ^ 70 +
        8910981164756711996821314076435873999241591315291938161284126668193247) * 10 ^ 70 +
        2312657359691958848132588166883287877195520696296249580144930437556515) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 7 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (246 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_246 :
    recurrence2Scalar2Main.coeff 246 =
      -((((300 * 10 ^ 70 +
        3929382145567216321715023357791996940091491964151079626851916368439638) * 10 ^ 70 +
        7368815885301956177167712095134783100388320898059550023763861884537079) * 10 ^ 70 +
        4621414459091651476817667414010911137341719951433943816194822993990822) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 6 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (247 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_247 :
    recurrence2Scalar2Main.coeff 247 =
      ((((305 * 10 ^ 70 +
        4563483203422858080376142991085755926170603836025319717850830306317971) * 10 ^ 70 +
        2410070757553127966947001605037918248762404463034645460386546386829852) * 10 ^ 70 +
        1478130197603326101506764219916030403962585062099199896997233843032979) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 5 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (248 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_248 :
    recurrence2Scalar2Main.coeff 248 =
      -((((285 * 10 ^ 70 +
        9146706222285465357169021296870294815833130050896016945532925864244436) * 10 ^ 70 +
        4998800810235124678102504285009115451923872773069828776547375686938654) * 10 ^ 70 +
        5436065484026581731765102975451396608383606969443254442929625979521851) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 4 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (249 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_249 :
    recurrence2Scalar2Main.coeff 249 =
      ((((250 * 10 ^ 70 +
        2858967922786557901508222906718293878769413793475702736337207239196918) * 10 ^ 70 +
        9617549653840754163224671855972175034678294761758220381733941958938874) * 10 ^ 70 +
        4960361592310852951747198963359776256473043723985991728762777274179206) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 3 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (250 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_250 :
    recurrence2Scalar2Main.coeff 250 =
      -((((206 * 10 ^ 70 +
        6679114521589218728541989833635381295787684887047766650855184523942814) * 10 ^ 70 +
        2967232482121728893792825753803329916769803218960135031320614547076973) * 10 ^ 70 +
        6324769543020167046239866264500983127283975208252706140479428532227822) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 2 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (251 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_251 :
    recurrence2Scalar2Main.coeff 251 =
      ((((161 * 10 ^ 70 +
        7395836996666963040279712827333696745016066001047208635388180357077331) * 10 ^ 70 +
        6001737385750607520002633325470584237860068877228386264554186550761286) * 10 ^ 70 +
        3087677975575601145227256735930743819151432872582302993019776553642492) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 106 = 1 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (252 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_252 :
    recurrence2Scalar2Main.coeff 252 =
      -((((120 * 10 ^ 70 +
        2591652292001421673738072577643782811848705216780326481731857229876621) * 10 ^ 70 +
        2405385727024528884357839302174865905342915961665769437345738635025552) * 10 ^ 70 +
        2491562731376198099159444450977287559309643465126098478454254913436501) : ℚ) := by
  unfold recurrence2Scalar2Main
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
  rw [recurrence2Scalar2Main_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (253 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_253 :
    recurrence2Scalar2Main.coeff 253 =
      ((((85 * 10 ^ 70 +
        0127023231615946489245279924690636287897233007413913961667304755972412) * 10 ^ 70 +
        9962130694019225641126605175024242474405452350644422374946924140269906) * 10 ^ 70 +
        4176669469458155470530538846170892465703735992372860569033077985470691) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 31 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (254 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_254 :
    recurrence2Scalar2Main.coeff 254 =
      -((((57 * 10 ^ 70 +
        0879794791221167274606581453306909897605774402799889758887801726938193) * 10 ^ 70 +
        3823146955875583318854077907158479816911615996268960681541629749094179) * 10 ^ 70 +
        0483801769374272475503905594523172838326578568317065064384985316201519) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 30 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (255 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_255 :
    recurrence2Scalar2Main.coeff 255 =
      ((((36 * 10 ^ 70 +
        3222901045619399152942558960779553518710294591602988345887064673901025) * 10 ^ 70 +
        4393558224828399448725655938825051012390405963857232024153930121588244) * 10 ^ 70 +
        5927457096775028700065909001003078718619298661700412005678731602115455) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 29 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (256 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_256 :
    recurrence2Scalar2Main.coeff 256 =
      -((((21 * 10 ^ 70 +
        7867773783207851916404120753413699682475284844958014946146336425585402) * 10 ^ 70 +
        8531314619872103957008780490748765292250515052737650825404506840902368) * 10 ^ 70 +
        8369430597449957584771575803990620327735877686812992907572986461774171) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 28 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (257 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_257 :
    recurrence2Scalar2Main.coeff 257 =
      ((((12 * 10 ^ 70 +
        2096205803568329953697892443848493373835885339929706714105715702953607) * 10 ^ 70 +
        2624642156054541932532830553545044324916257341505296533874589961023513) * 10 ^ 70 +
        8893373123157238943240613618741079229665314267646792673412448721585380) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 27 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (258 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_258 :
    recurrence2Scalar2Main.coeff 258 =
      -((((6 * 10 ^ 70 +
        2872647485238986320891745094718418953397646675571830127836095278133123) * 10 ^ 70 +
        2240471610313851477718559988256696620053537236698405085771672263780682) * 10 ^ 70 +
        5030195613165256864359247051648458968869772312362802789857843475756799) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 26 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (259 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_259 :
    recurrence2Scalar2Main.coeff 259 =
      ((((2 * 10 ^ 70 +
        8736302384307627288257414308132597781962637818298911013553896791968848) * 10 ^ 70 +
        6823502181203169473885041636490438132946160229315585343840522921246811) * 10 ^ 70 +
        5871411405118630366229882890489226820042383277699173519956911290502837) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 25 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (260 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_260 :
    recurrence2Scalar2Main.coeff 260 =
      -((((1 * 10 ^ 70 +
        0646149688787783331975300807417545314082030208935338744643879929994253) * 10 ^ 70 +
        4832193618793649741880250342872093626234301500384585570696529569332602) * 10 ^ 70 +
        1826577650916793352059252511172940838187405225168034030113052158343884) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 24 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (261 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_261 :
    recurrence2Scalar2Main.coeff 261 =
      (((2080563506824725241279737762665012152538943823498590024926830996281602 * 10 ^ 70 +
        8701908041395747777373901145771469368191696170374536750607708828108550) * 10 ^ 70 +
        1317077833761304533357965733385843829309714195523523850425329769477025) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 23 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (262 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_262 :
    recurrence2Scalar2Main.coeff 262 =
      (((1294545298286251269389786403081612955646276306144438471035355771070962 * 10 ^ 70 +
        1255041262909768289599333262438138932910960500345576762485557666641034) * 10 ^ 70 +
        9679413211387105644215447560932961063733461302309649038614228701763855) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 22 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (263 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_263 :
    recurrence2Scalar2Main.coeff 263 =
      -(((2133366282293718258325792650176873461204886366211041561153585922538699 * 10 ^ 70 +
        7159774227604857779867905087686548594866847546120484546515274099152739) * 10 ^ 70 +
        9488326844961246503161880955019488043676607066395647868071422532466852) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 21 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (264 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_264 :
    recurrence2Scalar2Main.coeff 264 =
      (((1922917882948710830475626444645933199810607125939671741879464617341951 * 10 ^ 70 +
        4099506234891871073730418836685904748882042364401154783497966253201648) * 10 ^ 70 +
        7866636222009772999292039498747569648636070758396003740936264713235586) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 20 +
      118 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (265 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_265 :
    recurrence2Scalar2Main.coeff 265 =
      -(((1410893631477453530744671499804053434269907252046802732932457513946303 * 10 ^ 70 +
        4589939956891086536202738999971999341401769635758971655945527282861520) * 10 ^ 70 +
        8079233373521984523233395799398182464365226451878558495796733889072327) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 19 +
      119 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (266 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_266 :
    recurrence2Scalar2Main.coeff 266 =
      (((919099552570439442252615216400915663921385651284079722486771761213615 * 10 ^ 70 +
        2800597582331910170531754966426790189009078357422131020726643009210528) * 10 ^ 70 +
        3284258665844795851959160237135743418504439825169359596454442002807002) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 18 +
      120 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (267 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_267 :
    recurrence2Scalar2Main.coeff 267 =
      -(((549492605826333407882961210611815299655168441778637131071375109697576 * 10 ^ 70 +
        9944929094852294696217252001963871655061176556215211061466118722919498) * 10 ^ 70 +
        8008107117930322571397285354956366644364244043193337826496706760303750) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 17 +
      121 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 35,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (268 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_268 :
    recurrence2Scalar2Main.coeff 268 =
      (((306264134988927724846051224589739375578853412532457048302878374613408 * 10 ^ 70 +
        7269898436994741459233732868367752234761133174906870407978875320470681) * 10 ^ 70 +
        6296351363050183821059458095627905473062443978479894295752273388353452) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 16 +
      122 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 36,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (269 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_269 :
    recurrence2Scalar2Main.coeff 269 =
      -(((160416191228229607576002654201804271262989758503174654874507711779999 * 10 ^ 70 +
        3145262093816529567985070014240301192539006848450796153918576819039640) * 10 ^ 70 +
        6658643560349355026489278304515435663328388607053701620915535606300065) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 15 +
      123 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 37,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (270 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_270 :
    recurrence2Scalar2Main.coeff 270 =
      (((79269134563272607497622516922769240461561776228289125732254659504768 * 10 ^ 70 +
        3587250585131834821245468999043176638782472780122475325634112443501839) * 10 ^ 70 +
        8785311811726272850418990685173905841671418360507317159859417295156067) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 14 +
      124 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 38,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (271 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_271 :
    recurrence2Scalar2Main.coeff 271 =
      -(((36995469238529394919541869624605459661737793804977916989209425633899 * 10 ^ 70 +
        1984866484586637685772219248781212948026717865583177193494170510588367) * 10 ^ 70 +
        5588399823950531777948145494523552312224499257720130217426386858902938) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 13 +
      125 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 39,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (272 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_272 :
    recurrence2Scalar2Main.coeff 272 =
      (((16286755835953961107401289383757614770636488225938084683423348058080 * 10 ^ 70 +
        9846462078480566108025319536085556334899341705487408965076709840669223) * 10 ^ 70 +
        2489788054572493840473493843563549717392693314471499925155176635644185) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 12 +
      126 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 40,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (273 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_273 :
    recurrence2Scalar2Main.coeff 273 =
      -(((6736729427519591723068259342610175420860900944764619599152659375707 * 10 ^ 70 +
        5069139077685111359564834232906381125459293268963484791936653288077757) * 10 ^ 70 +
        6916853609232619848648152943397266400066813789657553196374968829016117) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 11 +
      127 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 41,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (274 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_274 :
    recurrence2Scalar2Main.coeff 274 =
      (((2597652122574117012413339249683334226918273737451370057437930700291 * 10 ^ 70 +
        5613806658030564099352261365844268360048012147473751163361406989629126) * 10 ^ 70 +
        3602870453664607168425502118833316096209233251184276626692646777745701) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 10 +
      128 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 42,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (275 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_275 :
    recurrence2Scalar2Main.coeff 275 =
      -(((919939565792376187520826554769491900105751214555565449991646886935 * 10 ^ 70 +
        6221103345524840530521212368209707483400815872168235599527323086328317) * 10 ^ 70 +
        4607868860801230473779068245365478666917125999775743841043950492306791) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 9 +
      129 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 43,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (276 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_276 :
    recurrence2Scalar2Main.coeff 276 =
      (((290217167241892235343962841633880221395597480539480542223613853715 * 10 ^ 70 +
        4351645082687032969205075833156729298663707607245858697411590975650684) * 10 ^ 70 +
        0146485302160180449986969821164823476425982967700378227224792639702859) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 8 +
      130 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 44,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (277 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_277 :
    recurrence2Scalar2Main.coeff 277 =
      -(((75565402286759361810779654574298062912186197065765294006230912317 * 10 ^ 70 +
        1683547068607603409889921956173269500769366955479660303533334364590895) * 10 ^ 70 +
        1814403002323955317138399576446456566866285214497056795160144344873960) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 7 +
      131 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 45,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (278 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_278 :
    recurrence2Scalar2Main.coeff 278 =
      (((11905838933865149237596827828574198682008370488695388086783196204 * 10 ^ 70 +
        5238391538680619092552885736502147838508966685452244074990719817004991) * 10 ^ 70 +
        6796193007743938270229900376439577564630984817548794998728618435998445) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 6 +
      132 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 46,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (279 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_279 :
    recurrence2Scalar2Main.coeff 279 =
      (((2608980850721175394130750376366960404572321165167116184222181492 * 10 ^ 70 +
        9020957971763065491547727259410812034814472790045283040768215595016238) * 10 ^ 70 +
        1725485086159211814385718608156400925743369282860076407313351743889441) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 138 = 5 +
      133 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 47,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (280 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_280 :
    recurrence2Scalar2Main.coeff 280 =
      -(((3687282604064063503742719348563597201250266067237179900044947207 * 10 ^ 70 +
        7738597805537798700955130982655786473329520589804527060640843361220946) * 10 ^ 70 +
        0810590872300610268650212312286272050058675063171370409286865344201510) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rhs
    rw [show 138 = 4 +
      134 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 48,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (281 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_281 :
    recurrence2Scalar2Main.coeff 281 =
      (((2303130722895288423781007074838149267855092822390977930910093139 * 10 ^ 70 +
        5482467460416554302923152344695859504433608022250462728219504406923028) * 10 ^ 70 +
        4930590220150504413914523460445099995961524280453727682380538055553934) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 3 +
      135 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 49,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (282 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_282 :
    recurrence2Scalar2Main.coeff 282 =
      -(((1133512109024005592786304574314243075406491141769823352808949247 * 10 ^ 70 +
        1619756381611237287707629339120004656028606565418474261289023861820756) * 10 ^ 70 +
        8595063948590250807233807024287946177556314103333564353616031462991624) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 2 +
      136 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 50,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (283 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_283 :
    recurrence2Scalar2Main.coeff 283 =
      (((487447081059325913106266634841282040577515448187192335325747769 * 10 ^ 70 +
        9569006855622266171741675398003516770968079262628041188267542421989434) * 10 ^ 70 +
        2581587156976798096763550191797886775608471619282085753657320762544138) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 1 +
      137 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 51,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (284 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_284 :
    recurrence2Scalar2Main.coeff 284 =
      -(((189948169448797051263018753641285010000057339780862565595011535 * 10 ^ 70 +
        0945759357536562672415866660865471210107865854646210525456132689051336) * 10 ^ 70 +
        6520917838347474930879716032584845611174862601144227451695407680627159) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 52,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (285 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_285 :
    recurrence2Scalar2Main.coeff 285 =
      (((68122893774986056522016523390946856109108719673402128444139261 * 10 ^ 70 +
        0949965392736071092155993315148700209976851953222505407451334386780605) * 10 ^ 70 +
        3088596567078243695891003177358384198236706740242953280246235879287118) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 31 +
      139 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 53,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (286 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_286 :
    recurrence2Scalar2Main.coeff 286 =
      -(((22623937723339795972969438327380893302678311036722831923501712 * 10 ^ 70 +
        2652446082395787409100943665445858198246986056102552159469617047811637) * 10 ^ 70 +
        1254508507102505961408643831484406486342116231542785851560869156236084) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 30 +
      140 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 54,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (287 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_287 :
    recurrence2Scalar2Main.coeff 287 =
      (((6959588919816405881803990376468750781651287798525380472550904 * 10 ^ 70 +
        1181719650894681798316023612929582750841994361400184244876455675642540) * 10 ^ 70 +
        8647216941874172565104076435769384768032561028189896897398069636437957) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 29 +
      141 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 55,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (288 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_288 :
    recurrence2Scalar2Main.coeff 288 =
      -(((1972977258346864230919998697669466957305710968875864774492505 * 10 ^ 70 +
        3704662267155887872953170821004814767565599559445658842731377029095631) * 10 ^ 70 +
        8039888416507433244136284600346322482587788567563056230897900414239813) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 28 +
      142 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 56,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (289 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_289 :
    recurrence2Scalar2Main.coeff 289 =
      (((509017686387898206280465607481312262506373173096035175182971 * 10 ^ 70 +
        2509965552068018384900421269243384673763413612487840093065885068135670) * 10 ^ 70 +
        5639011945910309599327476976446163532879986455064314686465452593771701) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 27 +
      143 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 57,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (290 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_290 :
    recurrence2Scalar2Main.coeff 290 =
      -(((116320384773557593605408958506766967039692822701938921044108 * 10 ^ 70 +
        0234129830690233992262386322595523709071991239054087501573037460583467) * 10 ^ 70 +
        6932743823044777240698198361979221625645029067545333688237498426164691) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 26 +
      144 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 58,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (291 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_291 :
    recurrence2Scalar2Main.coeff 291 =
      (((22031820569202299019410788020244606839505996074870224739221 * 10 ^ 70 +
        5684623888406384067825627395899675847631644318203281448410372691922667) * 10 ^ 70 +
        6014213940276636091465440974150320369077449360029256699751846047868989) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 25 +
      145 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 59,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (292 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_292 :
    recurrence2Scalar2Main.coeff 292 =
      -(((2708539723630014127784335861591647173990984240127567417741 * 10 ^ 70 +
        1420111803949631441321055483514703226296849444755680806705466262700871) * 10 ^ 70 +
        8322918195360946599068384572675459758448463247013443900599854274358067) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 24 +
      146 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 60,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (293 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_293 :
    recurrence2Scalar2Main.coeff 293 =
      -(((214763526904120708318864494479698773220776241418406368043 * 10 ^ 70 +
        7240945744604641698415919102068987173786253174853639174154021477451139) * 10 ^ 70 +
        1400949841806279307153508800090686146782169799387805157235222327384802) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 23 +
      147 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 61,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 148,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (294 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_294 :
    recurrence2Scalar2Main.coeff 294 =
      (((294897427974398387339966268625694863092444697554211585656 * 10 ^ 70 +
        0684755078200266040535663879504540792090079808924109476660470712958570) * 10 ^ 70 +
        9089247190482700232840197045645164583674601390245303864624231272203605) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 22 +
      148 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 62,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 149,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (295 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_295 :
    recurrence2Scalar2Main.coeff 295 =
      -(((129234899516867506299605031844380419025265039297432697028 * 10 ^ 70 +
        4149999310865022988867574189154490305672823291760117759285486933231938) * 10 ^ 70 +
        6282374233848907262178654701131795819829384915085830349635595728595695) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 21 +
      149 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 63,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 150,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (296 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_296 :
    recurrence2Scalar2Main.coeff 296 =
      (((42700250108501245101660528773708315298090270907663510139 * 10 ^ 70 +
        5441013046448768769692318007792303007713177718601507937769254910987203) * 10 ^ 70 +
        4411659045219303362605879535079353373578275158913839666751444713505321) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 20 +
      150 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 64,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 151,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (297 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_297 :
    recurrence2Scalar2Main.coeff 297 =
      -(((11984458886787335292907275927683051870756298346568486403 * 10 ^ 70 +
        2774026373439971913399646028564823880791994457665246003969840231659942) * 10 ^ 70 +
        9032638420951608054740782492514367142668436944515628917412352041209083) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 19 +
      151 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 65,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 152,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (298 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_298 :
    recurrence2Scalar2Main.coeff 298 =
      (((2963087577230663999902592914611915421387693680980808679 * 10 ^ 70 +
        3276970036341246213456096570753103402475416596117258835224697940839909) * 10 ^ 70 +
        7447116568473837746194752068375728455305271235442238649112857510798311) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 18 +
      152 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 66,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (299 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_299 :
    recurrence2Scalar2Main.coeff 299 =
      -(((651647566002975579898403260187225410391270624931155849 * 10 ^ 70 +
        9206894081042413441621992575139954665414005660562738465017142120371779) * 10 ^ 70 +
        6331778137635623502857182538559297193432082361370981716942770837404619) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 17 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 67,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (300 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_300 :
    recurrence2Scalar2Main.coeff 300 =
      (((126643657052687210820113998274623964463639203294706105 * 10 ^ 70 +
        8377499067805879290773443927537832353208645364698753858100224717405293) * 10 ^ 70 +
        8359129600500241195003265526427015225318906615807333201204915246266917) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 16 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 68,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (301 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_301 :
    recurrence2Scalar2Main.coeff 301 =
      -(((21170464373738621892723282400915707765604654725164029 * 10 ^ 70 +
        2005354607375025425456917305518630485240482709692101557585360032489103) * 10 ^ 70 +
        4702688822338671606791305001056985051113400284071334708839983236289638) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 15 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 69,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (302 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_302 :
    recurrence2Scalar2Main.coeff 302 =
      (((2818335266513672689544564166152887145049835559013146 * 10 ^ 70 +
        8851955079167670353410343981724639008009727751827563472554543562439305) * 10 ^ 70 +
        1706840579806917838185816404055225571502274725558103928006059568010926) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 14 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (303 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_303 :
    recurrence2Scalar2Main.coeff 303 =
      -(((215211361399415567351107272315201589794950755209094 * 10 ^ 70 +
        5468231022731365246238259831858174014361189181265772854079073273678389) * 10 ^ 70 +
        7285878249979574234362483347417020387843812891813938018922962558350954) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 13 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (304 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_304 :
    recurrence2Scalar2Main.coeff 304 =
      -(((25655088010431365572279143252609254877993547523339 * 10 ^ 70 +
        4991214762932108103032254120192317444069406465036455732049901020945573) * 10 ^ 70 +
        0400648382987599903447669309751784866098411133861976379550508652164103) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 12 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (305 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_305 :
    recurrence2Scalar2Main.coeff 305 =
      (((15928205103947592158422555561978224296959340630963 * 10 ^ 70 +
        7627673275098542902887748802610820397293858007146128938800934595181507) * 10 ^ 70 +
        2708240677275150731636783017645421963308277289821177729452356014142166) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 11 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (306 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_306 :
    recurrence2Scalar2Main.coeff 306 =
      -(((4386959081253642078921110532638695914016023872308 * 10 ^ 70 +
        0217753332414880242100993587655289596256044244120374823897694434253429) * 10 ^ 70 +
        5531971709012769387273348949705061796351704254456888681862653796668911) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 10 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (307 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_307 :
    recurrence2Scalar2Main.coeff 307 =
      (((908386340541312841417722561243374984341361805048 * 10 ^ 70 +
        6997534597457597111477425646916549156792054022375932149369079949603527) * 10 ^ 70 +
        3431065356562711706644030046578271843926203922449257977122634309717070) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 9 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (308 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_308 :
    recurrence2Scalar2Main.coeff 308 =
      -(((153727892576582970625211646249494666110700947070 * 10 ^ 70 +
        3157952867407460386507911986304199040171756788017394661227110249057387) * 10 ^ 70 +
        0483636170183262964824708151644094313627477382281470135241732373973273) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 8 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (309 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_309 :
    recurrence2Scalar2Main.coeff 309 =
      (((21329511856300208254493206760136018560227106608 * 10 ^ 70 +
        0730987901528999335091067310461525559611321201537574160405723832882486) * 10 ^ 70 +
        8451602782769578004067846330579687732620320466505618904751268241749227) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 7 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (310 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_310 :
    recurrence2Scalar2Main.coeff 310 =
      -(((2273737809544632903579334343738194693119385637 * 10 ^ 70 +
        0258170183160269288938669151556383570319479619864942123363741459735350) * 10 ^ 70 +
        7941333621010097839434944111818590020695005990597597449091659672030240) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 6 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (311 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_311 :
    recurrence2Scalar2Main.coeff 311 =
      (((134214532129183609346247028275748579473234880 * 10 ^ 70 +
        9024370769590953138088075606963309203360134921909464474168343701022030) * 10 ^ 70 +
        2162553730386723286667795181185887992749992034386646953055127790633408) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 170 = 5 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (312 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_312 :
    recurrence2Scalar2Main.coeff 312 =
      (((12493424611427153331723093530042274950986344 * 10 ^ 70 +
        2725885380839457228711446693456085468073345574437023874542682530203666) * 10 ^ 70 +
        1915751790479403540664216535013896867132779670421623625448440027984032) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rhs
    rw [show 170 = 4 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (313 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_313 :
    recurrence2Scalar2Main.coeff 313 =
      -(((5623120651188670557216490603122332544579835 * 10 ^ 70 +
        5009011802452248627798316418850390195461864112543017447373758251070684) * 10 ^ 70 +
        5892977886891049393813272068943568446527707148331420432777078992408624) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 3 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (314 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_314 :
    recurrence2Scalar2Main.coeff 314 =
      (((1094627725689114679939767731310066714665936 * 10 ^ 70 +
        8613430256961959816411554316216628310232233787158288573508804359368898) * 10 ^ 70 +
        6876170679520880940546423002959395085770768215571139520602774105655519) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 2 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (315 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_315 :
    recurrence2Scalar2Main.coeff 315 =
      -(((152322329276388894703369238461401004621429 * 10 ^ 70 +
        2071727273759022031729247174845498340554286329096792651829175919794879) * 10 ^ 70 +
        2072902017167960799491923996379719192616435017194247746103673328365149) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 1 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (316 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_316 :
    recurrence2Scalar2Main.coeff 316 =
      (((15819122470015665910992181377801554309292 * 10 ^ 70 +
        6879864347272926119564600229840575905641830316120438654097142405459297) * 10 ^ 70 +
        0602524327239836364990104917267582970435763648925864573508362915964892) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (317 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_317 :
    recurrence2Scalar2Main.coeff 317 =
      -(((1062186299827485473260143374495715951985 * 10 ^ 70 +
        8190507185592081405625976989047999636488739421269874205430186847035961) * 10 ^ 70 +
        7735853662510747333926469955350307212687431782032580374301082840224305) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 31 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (318 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_318 :
    recurrence2Scalar2Main.coeff 318 =
      -(((3277274167399156481628990860054198686 * 10 ^ 70 +
        8399683847141329859111034426049221386923083304450282620486716418075408) * 10 ^ 70 +
        9270479854303926060135031995360199710292642127739598048935096308036830) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 30 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (319 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_319 :
    recurrence2Scalar2Main.coeff 319 =
      (((14052810434814592773488023583126804356 * 10 ^ 70 +
        6447120347516446576348628795275991725501857932312943297203123445754813) * 10 ^ 70 +
        3833343933953923181915030688551532504725252350260330989643622014350673) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 29 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (320 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_320 :
    recurrence2Scalar2Main.coeff 320 =
      -(((2542839945280669067068779188464862129 * 10 ^ 70 +
        6857849923422792389498570921546401530915180192915882748837986182681112) * 10 ^ 70 +
        4326370489746372772049067422101734539919500642544068242493471145099284) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 28 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (321 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_321 :
    recurrence2Scalar2Main.coeff 321 =
      (((295948849442373561357637745468246236 * 10 ^ 70 +
        6579984425521036463205478091040163134742478981212887897483290523553486) * 10 ^ 70 +
        0263116087574954176364395147421694387111691756129375970903971006585724) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 27 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (322 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_322 :
    recurrence2Scalar2Main.coeff 322 =
      -(((24710175853541087079412258605580274 * 10 ^ 70 +
        0721931195676762484002714807196424711226250580945101510293940982412232) * 10 ^ 70 +
        1827977440969843812306317149317808464663648373121335104737272936925142) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 26 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (323 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_323 :
    recurrence2Scalar2Main.coeff 323 =
      (((1318067843596303020768019824171823 * 10 ^ 70 +
        4955282190335643988263266404502789172659911119371340205010922487843356) * 10 ^ 70 +
        3342963927825168248765157518894225136859643166183354123360205880495272) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 25 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (324 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_324 :
    recurrence2Scalar2Main.coeff 324 =
      -(((3440268919530050578897182983972 * 10 ^ 70 +
        7594123071135407788648519926287338364974265920186339717689481945214392) * 10 ^ 70 +
        9009862114180293073463305944877940585635150377962733642110885957196739) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 24 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (325 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_325 :
    recurrence2Scalar2Main.coeff 325 =
      -(((8612396978175425338299635825288 * 10 ^ 70 +
        7952397604936050040695237547512556002453747523208064048495573268117365) * 10 ^ 70 +
        5517516950473533206185401284673676909104151330845881785550274725559995) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 23 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (326 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_326 :
    recurrence2Scalar2Main.coeff 326 =
      (((1137800376346997074717370633265 * 10 ^ 70 +
        6270307366110326573780707870135769021608089403559152068625159929994570) * 10 ^ 70 +
        1109204244692620464787811483283567230180240331324369300644546239875809) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 22 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (327 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_327 :
    recurrence2Scalar2Main.coeff 327 =
      -(((91113373652381188597690792524 * 10 ^ 70 +
        1231599359758260903058147361686587757964822111519295372480622311096432) * 10 ^ 70 +
        3412942152055605559285595920246158234756362922431446171562884353253148) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 21 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (328 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_328 :
    recurrence2Scalar2Main.coeff 328 =
      (((4854101435780678867137455408 * 10 ^ 70 +
        6958051198896089101005677151646466941692374100146289079919406125039712) * 10 ^ 70 +
        1915634390641031943100230466982689542846080894929449585641126981106982) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 20 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (329 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_329 :
    recurrence2Scalar2Main.coeff 329 =
      -(((129484358716314561343049955 * 10 ^ 70 +
        5248290170096731013173709481002911288764758523226392088073889950400273) * 10 ^ 70 +
        5617462862894627022773460538635769623325604119233950363490147015244871) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 19 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (330 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_330 :
    recurrence2Scalar2Main.coeff 330 =
      -(((4834140668658228414622796 * 10 ^ 70 +
        2381709052288710624763333875077545610257970186017344995258530784940248) * 10 ^ 70 +
        8809803769509955877999670913271053538038894234458522808266203367822030) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 18 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (331 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_331 :
    recurrence2Scalar2Main.coeff 331 =
      (((812470723025451525638503 * 10 ^ 70 +
        0714266932153122161568777010869412299690523606483276697276677210589086) * 10 ^ 70 +
        5615215207595992939558384408823771199612657979247605745420280810932009) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 17 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (332 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_332 :
    recurrence2Scalar2Main.coeff 332 =
      -(((51781133944453125770478 * 10 ^ 70 +
        2018884291292624209460456316632194113853888774350251383030210678397435) * 10 ^ 70 +
        8140836888662381089748873835881246055735220846084241528215786095279184) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 16 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (333 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_333 :
    recurrence2Scalar2Main.coeff 333 =
      (((1933271236309310659642 * 10 ^ 70 +
        4358302118899262565506374346696887937381918037156248304679024788282996) * 10 ^ 70 +
        5590257062998279798213994455944998277593251919053449117227180812887720) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 15 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (334 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_334 :
    recurrence2Scalar2Main.coeff 334 =
      -(((29788584645904823362 * 10 ^ 70 +
        5921042944680545484185039213940110634970834429435250646879398366463319) * 10 ^ 70 +
        1697767399389660911661252438723971863870519912154999836886104977962603) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 14 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (335 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_335 :
    recurrence2Scalar2Main.coeff 335 =
      -(((1216519198774344766 * 10 ^ 70 +
        6646633470664584609493074557394472002154989818695760980301716601851023) * 10 ^ 70 +
        6108598999330270694330817342780544502405429634534461022920093523208390) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 13 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (336 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_336 :
    recurrence2Scalar2Main.coeff 336 =
      (((98711194334625607 * 10 ^ 70 +
        0239722173047649738846032839511052751195331784676158871118841948302414) * 10 ^ 70 +
        5043221868932920126344327952838464598915450543025680109667129642048246) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 12 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (337 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_337 :
    recurrence2Scalar2Main.coeff 337 =
      -(((3168224069642583 * 10 ^ 70 +
        1654390563671621239163998895305793906581644684972735033235382671948268) * 10 ^ 70 +
        6692646703441075721880617125409359004249885537522571617712933216517669) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 11 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (338 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_338 :
    recurrence2Scalar2Main.coeff 338 =
      (((42749094092037 * 10 ^ 70 +
        7349261696630370478484113023172077119798433567073471976497752897805366) * 10 ^ 70 +
        3040694971606177036461271217995487404859270440095414708300093950149754) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 10 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (339 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_339 :
    recurrence2Scalar2Main.coeff 339 =
      (((605219502443 * 10 ^ 70 +
        8062606134850276551226079072138662613227451230151612766269800078727252) * 10 ^ 70 +
        1771289853334110269480421119672266835015369419686841732230380070139370) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 9 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (340 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_340 :
    recurrence2Scalar2Main.coeff 340 =
      -(((38281771593 * 10 ^ 70 +
        8222816862748036095594504127342120226611063719499301117352703924469305) * 10 ^ 70 +
        7510246432130502696826153772915537128206019036584982296081959570555769) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 8 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (341 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_341 :
    recurrence2Scalar2Main.coeff 341 =
      (((663021303 * 10 ^ 70 +
        9748615241039257352026470910976966690151525520885629980949499453449036) * 10 ^ 70 +
        8208343072554892410768474559387757285850644943310317436836182871925528) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 7 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (342 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_342 :
    recurrence2Scalar2Main.coeff 342 =
      -(((1494056 * 10 ^ 70 +
        7365298637413364192025636794011435075582701756270118905580927205792429) * 10 ^ 70 +
        2787278540758064467596584690870669888190079986295138246341636948136052) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 6 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (343 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_343 :
    recurrence2Scalar2Main.coeff 343 =
      -(((123981 * 10 ^ 70 +
        1569494618721921909263768837740908527507473866440412162763175324796806) * 10 ^ 70 +
        1566881402019436089572503327967703564884882710202427580745474883728932) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 5 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_343_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (344 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_344 :
    recurrence2Scalar2Main.coeff 344 =
      (((1750 * 10 ^ 70 +
        0659305172265827826654960018506642769151622325639083524269068719769816) * 10 ^ 70 +
        0738814636327312967556254934093623186442486121192588879099437551886688) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 4 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_344_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (345 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_345 :
    recurrence2Scalar2Main.coeff 345 =
      -((4582067153741661154198370094156679588145839382290741915415605322238610 * 10 ^ 70 +
        0279821981209881534869166573736503437259515537122763343289875715682159) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 3 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_345_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (346 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_346 :
    recurrence2Scalar2Main.coeff 346 =
      -((1699928389991809944570681786482199317010522823889880844807933320933648 * 10 ^ 70 +
        8151711812058491794675217296377519304482006188413197985181531592129466) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 2 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_346_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (347 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_347 :
    recurrence2Scalar2Main.coeff 347 =
      ((9568797926171031490751121382228950088351393623306119393532339064460 * 10 ^ 70 +
        5091421296747403896849086108238623889012397759998895056944755336975574) : ℚ) := by
  unfold recurrence2Scalar2Main
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
    rw [show 202 = 1 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_347_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (348 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_348 :
    recurrence2Scalar2Main.coeff 348 =
      ((63482887981909753055418875846658849208472659939121243189559946854 * 10 ^ 70 +
        8354352363536294558728287480449725021959591054502918814191302156889239) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 115 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_348_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (349 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_349 :
    recurrence2Scalar2Main.coeff 349 =
      -((658708750352099042077652902079075640717754004868983678274081398 * 10 ^ 70 +
        0592003779160617919119608231187762648767654617911886133839456612037362) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 116 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 31 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_349_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (350 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_350 :
    recurrence2Scalar2Main.coeff 350 =
      -((718610922935368930255760548893339138488142314564871344831922 * 10 ^ 70 +
        2835539268720972558599025246439049172579075562539265143436862198241346) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 117 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 30 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_350_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (351 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_351 :
    recurrence2Scalar2Main.coeff 351 =
      ((20801340065707979632504181495534192444946793376123281695882 * 10 ^ 70 +
        8256524976152564332633482556875073344509137908825400037071271054367560) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 118 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 29 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_351_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (352 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_352 :
    recurrence2Scalar2Main.coeff 352 =
      -((19108656801445271136296517028763780604967525751014623195 * 10 ^ 70 +
        0874719077182893297602704816241399429896147991685338739348059826241168) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 119 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 28 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_352_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (353 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_353 :
    recurrence2Scalar2Main.coeff 353 =
      -((348475338041420902186173018141948862051051829879406377 * 10 ^ 70 +
        2104061311576601032751930376920358986985953441929214990994594455182534) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 120 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 27 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_353_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (354 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_354 :
    recurrence2Scalar2Main.coeff 354 =
      ((758651038459824977928643864555364521840211724364823 * 10 ^ 70 +
        8166219520955626778721399757935022660080965759393945789536104480055205) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 121 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 26 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_354_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (355 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_355 :
    recurrence2Scalar2Main.coeff 355 =
      ((2903525564102000211346089595576848807594022556931 * 10 ^ 70 +
        9934021674515728750804223471736876301266523253373131462147472344883723) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 122 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 25 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_355_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (356 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_356 :
    recurrence2Scalar2Main.coeff 356 =
      -((10493511107294004193121499609540970450252531840 * 10 ^ 70 +
        5397483772281406603460579183414271886264897117993891235707974987027814) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 123 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 24 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_356_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (357 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_357 :
    recurrence2Scalar2Main.coeff 357 =
      -((6383671674769245183443374984942631284840361 * 10 ^ 70 +
        6894408667366659775361387118945913992092378260025735864075137633864524) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 124 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 23 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_357_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (358 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_358 :
    recurrence2Scalar2Main.coeff 358 =
      ((64547624422058934119922521924432086024769 * 10 ^ 70 +
        3917627655681924089440899830619229710755721178901421295677298080939521) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 125 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 22 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_358_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (359 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_359 :
    recurrence2Scalar2Main.coeff 359 =
      -((58635413568582134532486342604533092501 * 10 ^ 70 +
        5975782201520571813273061086633679797181674927034534622381951380257122) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 126 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 21 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_359_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (360 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_360 :
    recurrence2Scalar2Main.coeff 360 =
      -((120396854680381786529443252712262867 * 10 ^ 70 +
        6614917101736909736279792751894888373791120381206832063635398823874201) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 127 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 20 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_360_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (361 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_361 :
    recurrence2Scalar2Main.coeff 361 =
      ((285650490443634016221650512667481 * 10 ^ 70 +
        9212468555916688018224096354782420757048989499509761910087917273665430) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 128 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 19 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_361_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (362 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_362 :
    recurrence2Scalar2Main.coeff 362 =
      -((179899022256247105065369197532 * 10 ^ 70 +
        3939860258294187887595173047953275666569026442140167035878950989955348) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 129 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 18 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_362_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (363 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_363 :
    recurrence2Scalar2Main.coeff 363 =
      -((46212236993502372905608775 * 10 ^ 70 +
        1560944387032471545635261273953876539695391879036680781408342274919757) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 130 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 17 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_363_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (364 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_364 :
    recurrence2Scalar2Main.coeff 364 =
      ((112774955298695335734638 * 10 ^ 70 +
        4370962314920122341198235747776186017737073512333143548508083757073381) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 131 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 16 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_364_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (365 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_365 :
    recurrence2Scalar2Main.coeff 365 =
      -((53553483768967696044 * 10 ^ 70 +
        8123357039964095564269792865224808010253904993891644009361400282293093) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 132 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 15 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_365_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (366 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_366 :
    recurrence2Scalar2Main.coeff 366 =
      ((9496272400873665 * 10 ^ 70 +
        1414932051215604017837861682346463975271057420728255736086477001483127) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 133 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 14 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_366_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (367 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_367 :
    recurrence2Scalar2Main.coeff 367 =
      -((76487871421 * 10 ^ 70 +
        2366312323490153684099904590439724990542255361184021835999051289197600) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 134 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 13 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_367_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (368 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_368 :
    recurrence2Scalar2Main.coeff 368 =
      -((152740990 * 10 ^ 70 +
        6516013435785885931879464744645842366354508688492464266899716933083109) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 135 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 12 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_368_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (369 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_369 :
    recurrence2Scalar2Main.coeff 369 =
      ((15249 * 10 ^ 70 +
        4633668897125039491675253057536378732479819568076575598313429673864825) : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 136 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 11 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_369_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (370 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_370 :
    recurrence2Scalar2Main.coeff 370 =
      (-4852891461631037485158354673243426376137614182082606129331967617673851 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 137 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 10 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_370_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (371 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_371 :
    recurrence2Scalar2Main.coeff 371 =
      (45016138001732307997056916346578126364754345055308768370937396834 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 138 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 9 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_371_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (372 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_372 :
    recurrence2Scalar2Main.coeff 372 =
      (201812463031397670734903090380708852211071786471815315834222 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 139 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 8 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_372_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (373 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_373 :
    recurrence2Scalar2Main.coeff 373 =
      (-2556965889336893754564636540364248929695291549037498306 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 140 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 7 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_373_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (374 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_374 :
    recurrence2Scalar2Main.coeff 374 =
      (5696097295261880468386722689248325961965216045943 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 141 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 6 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_374_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (375 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_375 :
    recurrence2Scalar2Main.coeff 375 =
      (-1894078624154296784583223519827014096385232 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 142 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 5 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_375_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (376 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_376 :
    recurrence2Scalar2Main.coeff 376 =
      (156951811428646099285082056055836978 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 143 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 4 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_376_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 231,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (377 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_377 :
    recurrence2Scalar2Main.coeff 377 =
      (1419194059250961434935930168 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 144 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 3 +
      231 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_377_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 232,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (378 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_378 :
    recurrence2Scalar2Main.coeff 378 =
      (-3539242852643699596 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 379 = 145 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 2 +
      232 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_378_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar2Main_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient2.coeff x * recurrence2QuotientConstant.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Main_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 233,
      remainder3Coefficient2.coeff (147 + x) *
        recurrence2QuotientConstant.coeff (379 - (147 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B2_coeff_high (147 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Main_coeff_379 :
    recurrence2Scalar2Main.coeff 379 =
      (1911778728 : ℚ) := by
  unfold recurrence2Scalar2Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 380 = 146 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 1 +
      233 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Main_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Main_coeff_379_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
