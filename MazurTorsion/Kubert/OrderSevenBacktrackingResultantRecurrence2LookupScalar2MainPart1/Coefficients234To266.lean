/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB2
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2MainPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Main coefficient convolution

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
