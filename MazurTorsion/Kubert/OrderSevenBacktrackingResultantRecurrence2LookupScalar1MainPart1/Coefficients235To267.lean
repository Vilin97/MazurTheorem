/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupB1
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1MainPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Main coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2B1_coeff_0
  recurrence2B1_coeff_1
  recurrence2B1_coeff_2
  recurrence2B1_coeff_3
  recurrence2B1_coeff_4
  recurrence2B1_coeff_5
  recurrence2B1_coeff_6
  recurrence2B1_coeff_7
  recurrence2B1_coeff_8
  recurrence2B1_coeff_9
  recurrence2B1_coeff_10
  recurrence2B1_coeff_11
  recurrence2B1_coeff_12
  recurrence2B1_coeff_13
  recurrence2B1_coeff_14
  recurrence2B1_coeff_15
  recurrence2B1_coeff_16
  recurrence2B1_coeff_17
  recurrence2B1_coeff_18
  recurrence2B1_coeff_19
  recurrence2B1_coeff_20
  recurrence2B1_coeff_21
  recurrence2B1_coeff_22
  recurrence2B1_coeff_23
  recurrence2B1_coeff_24
  recurrence2B1_coeff_25
  recurrence2B1_coeff_26
  recurrence2B1_coeff_27
  recurrence2B1_coeff_28
  recurrence2B1_coeff_29
  recurrence2B1_coeff_30
  recurrence2B1_coeff_31
  recurrence2B1_coeff_32
  recurrence2B1_coeff_33
  recurrence2B1_coeff_34
  recurrence2B1_coeff_35
  recurrence2B1_coeff_36
  recurrence2B1_coeff_37
  recurrence2B1_coeff_38
  recurrence2B1_coeff_39
  recurrence2B1_coeff_40
  recurrence2B1_coeff_41
  recurrence2B1_coeff_42
  recurrence2B1_coeff_43
  recurrence2B1_coeff_44
  recurrence2B1_coeff_45
  recurrence2B1_coeff_46
  recurrence2B1_coeff_47
  recurrence2B1_coeff_48
  recurrence2B1_coeff_49
  recurrence2B1_coeff_50
  recurrence2B1_coeff_51
  recurrence2B1_coeff_52
  recurrence2B1_coeff_53
  recurrence2B1_coeff_54
  recurrence2B1_coeff_55
  recurrence2B1_coeff_56
  recurrence2B1_coeff_57
  recurrence2B1_coeff_58
  recurrence2B1_coeff_59
  recurrence2B1_coeff_60
  recurrence2B1_coeff_61
  recurrence2B1_coeff_62
  recurrence2B1_coeff_63
  recurrence2B1_coeff_64
  recurrence2B1_coeff_65
  recurrence2B1_coeff_66
  recurrence2B1_coeff_67
  recurrence2B1_coeff_68
  recurrence2B1_coeff_69
  recurrence2B1_coeff_70
  recurrence2B1_coeff_71
  recurrence2B1_coeff_72
  recurrence2B1_coeff_73
  recurrence2B1_coeff_74
  recurrence2B1_coeff_75
  recurrence2B1_coeff_76
  recurrence2B1_coeff_77
  recurrence2B1_coeff_78
  recurrence2B1_coeff_79
  recurrence2B1_coeff_80
  recurrence2B1_coeff_81
  recurrence2B1_coeff_82
  recurrence2B1_coeff_83
  recurrence2B1_coeff_84
  recurrence2B1_coeff_85
  recurrence2B1_coeff_86
  recurrence2B1_coeff_87
  recurrence2B1_coeff_88
  recurrence2B1_coeff_89
  recurrence2B1_coeff_90
  recurrence2B1_coeff_91
  recurrence2B1_coeff_92
  recurrence2B1_coeff_93
  recurrence2B1_coeff_94
  recurrence2B1_coeff_95
  recurrence2B1_coeff_96
  recurrence2B1_coeff_97
  recurrence2B1_coeff_98
  recurrence2B1_coeff_99
  recurrence2B1_coeff_100
  recurrence2B1_coeff_101
  recurrence2B1_coeff_102
  recurrence2B1_coeff_103
  recurrence2B1_coeff_104
  recurrence2B1_coeff_105
  recurrence2B1_coeff_106
  recurrence2B1_coeff_107
  recurrence2B1_coeff_108
  recurrence2B1_coeff_109
  recurrence2B1_coeff_110
  recurrence2B1_coeff_111
  recurrence2B1_coeff_112
  recurrence2B1_coeff_113
  recurrence2B1_coeff_114
  recurrence2B1_coeff_115
  recurrence2B1_coeff_116
  recurrence2B1_coeff_117
  recurrence2B1_coeff_118
  recurrence2B1_coeff_119
  recurrence2B1_coeff_120
  recurrence2B1_coeff_121
  recurrence2B1_coeff_122
  recurrence2B1_coeff_123
  recurrence2B1_coeff_124
  recurrence2B1_coeff_125
  recurrence2B1_coeff_126
  recurrence2B1_coeff_127
  recurrence2B1_coeff_128
  recurrence2B1_coeff_129
  recurrence2B1_coeff_130
  recurrence2B1_coeff_131
  recurrence2B1_coeff_132
  recurrence2B1_coeff_133
  recurrence2B1_coeff_134
  recurrence2B1_coeff_135
  recurrence2B1_coeff_136
  recurrence2B1_coeff_137
  recurrence2B1_coeff_138
  recurrence2B1_coeff_139
  recurrence2B1_coeff_140
  recurrence2B1_coeff_141
  recurrence2B1_coeff_142
  recurrence2B1_coeff_143
  recurrence2B1_coeff_144
  recurrence2B1_coeff_145
  recurrence2B1_coeff_146
  recurrence2B1_coeff_147
  recurrence2B1_coeff_148
  recurrence2B1_coeff_149
  recurrence2B1_coeff_150
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

private theorem recurrence2Scalar1Main_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 2,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (235 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_235 :
    recurrence2Scalar1Main.coeff 235 =
      -((((4096 * 10 ^ 70 +
        2082893075962217283925870183899038880267081796914842052567704199339640) * 10 ^ 70 +
        8208772037701378664389336621192250461093026669696366543594001690124137) * 10 ^ 70 +
        5229284107722884141487661184382885738051260247198391522464039205433724) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 21 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 3,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (236 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_236 :
    recurrence2Scalar1Main.coeff 236 =
      ((((4365 * 10 ^ 70 +
        1228554065547759951187053549284554733613616263818372361661202640879512) * 10 ^ 70 +
        3370020406969512434995770518252849159762763076091154512925018813449500) * 10 ^ 70 +
        4425262240106871375142864289951267810563579457038695697008701386037573) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 20 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 4,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (237 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_237 :
    recurrence2Scalar1Main.coeff 237 =
      -((((4398 * 10 ^ 70 +
        4846644526498622927632321676275701306339611040649402485223152390408107) * 10 ^ 70 +
        6749604967290583988210885481155170012591238864466666173225802845155996) * 10 ^ 70 +
        7538215389350341011167266922483873841896099364523630369254948226038541) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 19 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 5,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (238 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_238 :
    recurrence2Scalar1Main.coeff 238 =
      ((((4173 * 10 ^ 70 +
        3123262039851427531467883238530326877957809874192193564746094087768289) * 10 ^ 70 +
        2531221461915202169739162931695605403184897959075977263575515051876113) * 10 ^ 70 +
        4962225696017001320296082023247300734653525571989464812631475656277769) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 18 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 6,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (239 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_239 :
    recurrence2Scalar1Main.coeff 239 =
      -((((3698 * 10 ^ 70 +
        8714552099617417714007630631154020520438500389518839695086505316709366) * 10 ^ 70 +
        1459287388427575209996768620839198633090231378258946271718378715818900) * 10 ^ 70 +
        2229261842746312682847357080388618940796920206096950811768926336113415) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 17 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 7,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (240 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_240 :
    recurrence2Scalar1Main.coeff 240 =
      ((((3016 * 10 ^ 70 +
        7174750151902602169821813177094661894253335535783327739948926654310725) * 10 ^ 70 +
        7618191956050980954679475222551570391549792296630701311679289766877904) * 10 ^ 70 +
        5199257958084223702319867908650425113646733577450907566365939914382293) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 16 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 8,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (241 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_241 :
    recurrence2Scalar1Main.coeff 241 =
      -((((2194 * 10 ^ 70 +
        7259171196801948911016853764073373984858580486892322253914217831769937) * 10 ^ 70 +
        9841622381752400552153353370987281168362166869010049740292819499329954) * 10 ^ 70 +
        1303521859500026987237391961947973224885759066919143018479355064294845) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 15 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 9,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (242 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_242 :
    recurrence2Scalar1Main.coeff 242 =
      ((((1316 * 10 ^ 70 +
        2957751062927109707720179160913496359833141726729877963891253647644772) * 10 ^ 70 +
        5380562168676708849379216148385781557235997565991669722747184593632224) * 10 ^ 70 +
        8381749172388425641001305141595725328045576697793560047577196045906152) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 14 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 10,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (243 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_243 :
    recurrence2Scalar1Main.coeff 243 =
      -((((467 * 10 ^ 70 +
        0426893759347303083965585399500772297037239418338194077189625722913620) * 10 ^ 70 +
        8741346845168199569632710101690087079392856696614268179162804170761081) * 10 ^ 70 +
        0960216759072266519292659453770720829784028666022139912594046385031570) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 13 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 11,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (244 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_244 :
    recurrence2Scalar1Main.coeff 244 =
      -((((278 * 10 ^ 70 +
        1879638016087133038505487170816926321697686817269377406632633423166034) * 10 ^ 70 +
        5934803336903109903450806942807384021388671131733786821946366480427762) * 10 ^ 70 +
        1530673222824589491247545417660374943080562193320192118457918129498507) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 12 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_244_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 12,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (245 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_245 :
    recurrence2Scalar1Main.coeff 245 =
      ((((865 * 10 ^ 70 +
        3860196388379293984331178414424322874701703948924016712239238807252636) * 10 ^ 70 +
        6801121971993166673028024459484719290539974175803397155989199970380615) * 10 ^ 70 +
        3534484114450407840413806693731975869787966384742958681303905663523757) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 11 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_245_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 13,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (246 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_246 :
    recurrence2Scalar1Main.coeff 246 =
      -((((1266 * 10 ^ 70 +
        7818222639082220061548081444366896061247767873936473964944648265085278) * 10 ^ 70 +
        0642590285234650917113303942022774723141074563844722060554757327793110) * 10 ^ 70 +
        2137488634118456882139317825857482661885260226963458150715781173722457) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 10 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 14,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (247 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_247 :
    recurrence2Scalar1Main.coeff 247 =
      ((((1481 * 10 ^ 70 +
        0687254858275304530983205424094291878962991375327780014233061968368612) * 10 ^ 70 +
        8311387159441788030319055552169690566233340268084338064822920772280305) * 10 ^ 70 +
        3949606266953113163450254238750045930252214595699867194521194279289594) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 9 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 15,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (248 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_248 :
    recurrence2Scalar1Main.coeff 248 =
      -((((1529 * 10 ^ 70 +
        1222631921344218095908298059669534454361775402519916178532092928854801) * 10 ^ 70 +
        9585385378914822994770750695662770674941396976531026836493399246185424) * 10 ^ 70 +
        0116614403702666379246055804708705909723564022960762282482327616378239) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 8 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 16,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (249 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_249 :
    recurrence2Scalar1Main.coeff 249 =
      ((((1446 * 10 ^ 70 +
        7690867414160543739158735822650505593113268751101046854280090741299778) * 10 ^ 70 +
        3345089461569930828609777082939762041912538399302293854875469550995310) * 10 ^ 70 +
        2267859939979553433685549613537982840381535896652882960149597327062275) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 7 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 17,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (250 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_250 :
    recurrence2Scalar1Main.coeff 250 =
      -((((1276 * 10 ^ 70 +
        5234777561601781795754860277391254667588774227184444647377734162679694) * 10 ^ 70 +
        6752198657933738949530159997604305781844629922199693004238507683219042) * 10 ^ 70 +
        4373831110238916169889909548498603719349480410289889036190785948994457) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 6 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 18,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (251 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_251 :
    recurrence2Scalar1Main.coeff 251 =
      ((((1060 * 10 ^ 70 +
        0568620715386329557866361609665440268909060039266759682327439143171782) * 10 ^ 70 +
        2325674044821404730317595140517469338245296497638407755895491986859343) * 10 ^ 70 +
        0884288103008557681286720008999216863122760540971833229015543599902858) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 5 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 19,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (252 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_252 :
    recurrence2Scalar1Main.coeff 252 =
      -((((832 * 10 ^ 70 +
        6335203998331017620528901509070821721967047520518059119012924781949110) * 10 ^ 70 +
        2472730033802644284460267660724740548456242535694697320244523711947346) * 10 ^ 70 +
        5651846938533329372682850896931035026046641867598407289890562206148931) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 4 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 20,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (253 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_253 :
    recurrence2Scalar1Main.coeff 253 =
      ((((620 * 10 ^ 70 +
        0481104456783836600579715738040454982949973850308420024351777497263927) * 10 ^ 70 +
        5677923532597774045821977018109733251062508771514123290892627541726859) * 10 ^ 70 +
        3993760438173654796290753395320765754942924904979561646302418584234075) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 3 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 21,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (254 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_254 :
    recurrence2Scalar1Main.coeff 254 =
      -((((437 * 10 ^ 70 +
        9502611880576491169244681548255851152016598821153084737891185043304793) * 10 ^ 70 +
        1769083358691779947450173968031283399176718809089738178774068827263282) * 10 ^ 70 +
        9585751366840788661223592125632362849903552165604377214774219431115512) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 2 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 22,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (255 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_255 :
    recurrence2Scalar1Main.coeff 255 =
      ((((292 * 10 ^ 70 +
        9875744322938838782461310955308129692840460309273389578899259352773211) * 10 ^ 70 +
        3813852389009589465873872575207991546782745119045943757867077066621274) * 10 ^ 70 +
        1712976776133858232354225820154861462380352831497199113183191416183096) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 106 = 1 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 23,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (256 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_256 :
    recurrence2Scalar1Main.coeff 256 =
      -((((184 * 10 ^ 70 +
        9992954968669436493859390187158866714438074486230893174119246683392511) * 10 ^ 70 +
        6690351718490959125493662913762934754228138681997779662044542022837124) * 10 ^ 70 +
        4437581902483706269458794292398986406155358628187330100286311498854594) : ℚ) := by
  unfold recurrence2Scalar1Main
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
  rw [recurrence2Scalar1Main_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 24,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (257 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_257 :
    recurrence2Scalar1Main.coeff 257 =
      ((((109 * 10 ^ 70 +
        5236873297834168545340052253345608532846633893358869548301436328476599) * 10 ^ 70 +
        7248388347975856056527139757966563885985341037167637719202502356065792) * 10 ^ 70 +
        9237659754198656735638774091080802301060718626587140946988508748841859) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 31 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 25,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (258 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_258 :
    recurrence2Scalar1Main.coeff 258 =
      -((((60 * 10 ^ 70 +
        0649729157059450671504987947721047001853910349732250635022413225633181) * 10 ^ 70 +
        7848020241915006927974130802587642336492745423484340626666071797849312) * 10 ^ 70 +
        7310902725618307775271725449605949460689357023194237327976743859785084) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 30 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 26,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (259 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_259 :
    recurrence2Scalar1Main.coeff 259 =
      ((((29 * 10 ^ 70 +
        8076623382197473795128201189299096517012096844989337520554655546301268) * 10 ^ 70 +
        6927240526015813556089794920275642279999094787728143079545244098769719) * 10 ^ 70 +
        7366851870530670708720421375783106778528030823131543644871330165705078) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 29 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 27,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (260 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_260 :
    recurrence2Scalar1Main.coeff 260 =
      -((((12 * 10 ^ 70 +
        6896595241220218332555925626656016082650362496570612366955087053457687) * 10 ^ 70 +
        3956507535059168826701575441998323901844928126964904689627800983820954) * 10 ^ 70 +
        8482246946901842827804443226425551042098906747882484858202320835906286) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 28 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 28,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (261 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_261 :
    recurrence2Scalar1Main.coeff 261 =
      ((((3 * 10 ^ 70 +
        9048292723968752546727977571896232149945324728233453415127148506760213) * 10 ^ 70 +
        6841932475415129372657520959856791820578455428144162102208853265507555) * 10 ^ 70 +
        5810661485132578165266039025794795277499409346293015401566134591551809) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 27 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 29,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (262 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_262 :
    recurrence2Scalar1Main.coeff 262 =
      (((122439177466713039702019100012575315120519123173191214586796690951314 * 10 ^ 70 +
        7688468150864059466032312552727757515647187182063104528838034663963605) * 10 ^ 70 +
        1179816400556569128527466852867594468534323058019467865221042201412529) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 26 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 30,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (263 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_263 :
    recurrence2Scalar1Main.coeff 263 =
      -((((1 * 10 ^ 70 +
        3503773843069112610896951935998250211632970567919154067187127931267501) * 10 ^ 70 +
        1309348005585294287179681624660235644602837850884263027876110674656217) * 10 ^ 70 +
        5537086886249322861029125893081512692975768522003922367188581157431869) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 25 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 31,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (264 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_264 :
    recurrence2Scalar1Main.coeff 264 =
      ((((1 * 10 ^ 70 +
        4922398435997782913308460092033835487528414500252538918347807655645173) * 10 ^ 70 +
        7334803721633759903139326733646582238205338954756552710083596894931149) * 10 ^ 70 +
        9434797459870710346919439439059321054641660139102421976383462142884682) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 24 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 32,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (265 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_265 :
    recurrence2Scalar1Main.coeff 265 =
      -((((1 * 10 ^ 70 +
        1933187331609026927893435433166409094642894249486465959187633635909486) * 10 ^ 70 +
        2097803706427840563755802620512311583202676082412430403545111674280149) * 10 ^ 70 +
        9191895774106835087834406625783327447298827746955959899058376396805626) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 23 +
      115 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 33,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (266 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_266 :
    recurrence2Scalar1Main.coeff 266 =
      (((8163704262503732913354300215683498571593836810073344753061547979364445 * 10 ^ 70 +
        8082272965896262011490984943422064422831050276466493048650103190119226) * 10 ^ 70 +
        8785647793872775018835325571878255712229514629182571440515883998369988) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 22 +
      116 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 34,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (267 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_267 :
    recurrence2Scalar1Main.coeff 267 =
      -(((5029492904395262397738265546831104388201411728900319851851764503001455 * 10 ^ 70 +
        3341328064315923855600578466197325237117224155850094475532576771963732) * 10 ^ 70 +
        9060743664591000106746956322801999954583864440966394413590336252584061) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 138 = 21 +
      117 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
