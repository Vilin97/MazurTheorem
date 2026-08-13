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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
