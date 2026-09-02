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

private theorem recurrence2Scalar1Main_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 70,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 153,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (303 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_303 :
    recurrence2Scalar1Main.coeff 303 =
      -(((6450090432958324587763034404741638943435917136470162 * 10 ^ 70 +
        3934587375121175080553305079829883394160625165373738511616364579950194) * 10 ^ 70 +
        6021867118322284325924735198101474796941419553616292984403930491011130) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 17 +
      153 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 71,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 154,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (304 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_304 :
    recurrence2Scalar1Main.coeff 304 =
      (((5779203274871504473939480306201448418446151879824757 * 10 ^ 70 +
        0281507904351783158683462427152990502464927536668617057469804771247952) * 10 ^ 70 +
        6826250172240601142521554916483819676306087803890209474277751880041436) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 16 +
      154 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 72,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 155,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (305 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_305 :
    recurrence2Scalar1Main.coeff 305 =
      -(((1960119551363546757334708467579131794528099106029179 * 10 ^ 70 +
        1052482829963891501574550201682484389892726580272937112962034650279687) * 10 ^ 70 +
        7989602638618267317018232545657641060622081527313565269751450003165647) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 15 +
      155 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 73,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 156,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (306 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_306 :
    recurrence2Scalar1Main.coeff 306 =
      (((487530779654419217619530951968461404561952780095391 * 10 ^ 70 +
        2843722737743558849765877642771252781798727241519159943255192407939191) * 10 ^ 70 +
        2989582547237962774031339165413171833243876775048655547340405175935386) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 14 +
      156 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 74,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 157,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (307 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_307 :
    recurrence2Scalar1Main.coeff 307 =
      -(((97381771249800552550954307910271117917636268625635 * 10 ^ 70 +
        5175682608372888167581598777280739113217642032445638271438431312257082) * 10 ^ 70 +
        8527149068576148004947292855684791312628927956103256944293185171264654) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 13 +
      157 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 75,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 158,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (308 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_308 :
    recurrence2Scalar1Main.coeff 308 =
      (((15526669165083472395213059560437249814462776306812 * 10 ^ 70 +
        9329315590393787341178820240622761958476994926426677715538729854612010) * 10 ^ 70 +
        7964789142308388162774274690397226753622642275591187980671969802684922) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 12 +
      158 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 76,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 159,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (309 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_309 :
    recurrence2Scalar1Main.coeff 309 =
      -(((1761758718206354150811781856917563926564047664781 * 10 ^ 70 +
        1282775080311451220727910957761084266283733623067226186097510060542360) * 10 ^ 70 +
        1040900245243167613611751049845608145895458610702247027056267509796955) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 11 +
      159 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 77,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 160,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (310 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_310 :
    recurrence2Scalar1Main.coeff 310 =
      (((51889744475777608265718376166839647651324771617 * 10 ^ 70 +
        6244749086127005623999589739430759050356976980058179148384220558140851) * 10 ^ 70 +
        1863081118749568162393419569613337087450270683701780259570907889460267) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 10 +
      160 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 78,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 161,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (311 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_311 :
    recurrence2Scalar1Main.coeff 311 =
      (((39697730346914821578828751706281904743102294744 * 10 ^ 70 +
        0104420639052907017638726598927370918981279143568852677384193642836267) * 10 ^ 70 +
        3200340306824602375928150631777814822781591599086743967747645094139430) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 9 +
      161 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 79,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 162,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (312 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_312 :
    recurrence2Scalar1Main.coeff 312 =
      -(((13740159818404412443750336707627252654376481891 * 10 ^ 70 +
        7173153335649494147433970032764270436260290331906881642065710677087567) * 10 ^ 70 +
        6197616830811000195466475612699265613454036096166917039780817573788622) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 8 +
      162 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 80,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 163,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (313 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_313 :
    recurrence2Scalar1Main.coeff 313 =
      (((2962589837468223407070800093653755900873713111 * 10 ^ 70 +
        3259429362745553878574727787281863209551969602156986574601133418815643) * 10 ^ 70 +
        5341434931026278631650400298190632564042667803149842187181014400283527) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 7 +
      163 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 81,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 164,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (314 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_314 :
    recurrence2Scalar1Main.coeff 314 =
      -(((488532780767606520620876953641486171914405710 * 10 ^ 70 +
        0749624536758118943187565534203156455170024609835047450948971211637632) * 10 ^ 70 +
        5918286226627246754646297745477418860075956000476987842892965310214365) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 6 +
      164 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 82,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 165,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (315 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_315 :
    recurrence2Scalar1Main.coeff 315 =
      (((62714800952022312916902773459548678281726704 * 10 ^ 70 +
        7461036309433402696665914950938834358706237302834480563762374041478087) * 10 ^ 70 +
        2335124832783051490207250094742818840495732456724487037362215026389025) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 170 = 5 +
      165 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 83,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 166,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (316 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_316 :
    recurrence2Scalar1Main.coeff 316 =
      -(((5660200639059507616012700337427189414307150 * 10 ^ 70 +
        2059340125820341101436318460976235454078214320361376637828168349019771) * 10 ^ 70 +
        7879327779993741476432555353245749907344505703564527997972474652925888) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rhs
    rw [show 170 = 4 +
      166 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 84,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 167,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (317 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_317 :
    recurrence2Scalar1Main.coeff 317 =
      (((149839267117240727819235554511159247146172 * 10 ^ 70 +
        6675848433884798788605420731247501044750113174234868295508087387019129) * 10 ^ 70 +
        9476956012255925523470781635427361346050127521036613266083058312893487) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 3 +
      167 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 85,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 168,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (318 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_318 :
    recurrence2Scalar1Main.coeff 318 =
      (((68141227635070960871813531263733121285858 * 10 ^ 70 +
        8912913332916002987297001969946227298522805075881863836763335217615562) * 10 ^ 70 +
        5390425942868135704368207069214972547488153661336567810813397018937055) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 2 +
      168 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 86,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 169,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (319 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_319 :
    recurrence2Scalar1Main.coeff 319 =
      -(((17745877016124153142133207449636719710407 * 10 ^ 70 +
        1418428334734056946928120217232324878596885561277124012669990377591173) * 10 ^ 70 +
        1405809034946984812853514952517067861045115801626132055342002450997459) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 1 +
      169 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 87,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 170,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (320 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_320 :
    recurrence2Scalar1Main.coeff 320 =
      (((2721035712270283247121455316902967452447 * 10 ^ 70 +
        0661188888257550288129034058176364315444553527080332353544364869025948) * 10 ^ 70 +
        6575347198000311190428550620040471330531594033144555103310718983491441) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 88,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 171,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (321 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_321 :
    recurrence2Scalar1Main.coeff 321 =
      -(((297755540244667526559078258933407676234 * 10 ^ 70 +
        1918763956604527438483792991439667427263304748806487981384165010254496) * 10 ^ 70 +
        2102553297114591141207355132495902314628796700167679384603450904270894) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 31 +
      171 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 89,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 172,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (322 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_322 :
    recurrence2Scalar1Main.coeff 322 =
      (((21520026781288169721137337411521440650 * 10 ^ 70 +
        6729277649679389439524771816101417319305313900197609689257160654499529) * 10 ^ 70 +
        6737304271070186874378055726139175839032865212874220717573538891994351) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 30 +
      172 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 90,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 173,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (323 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_323 :
    recurrence2Scalar1Main.coeff 323 =
      -(((312637191860920648293130885138634504 * 10 ^ 70 +
        1876855675143147620934585298624244305877275629593915779122550844089138) * 10 ^ 70 +
        0854016782300778717430785936285158734960215544406314241731359089178967) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 29 +
      173 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 91,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 174,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (324 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_324 :
    recurrence2Scalar1Main.coeff 324 =
      -(((190880915396306214883834881756756868 * 10 ^ 70 +
        1540064885276574109173821912514475242013098991067761950561900723498381) * 10 ^ 70 +
        1682617708696866995256421998731478459429167685960974865859905045974879) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 28 +
      174 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 92,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 175,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (325 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_325 :
    recurrence2Scalar1Main.coeff 325 =
      (((35707040607585651452890159599162930 * 10 ^ 70 +
        9777598571436802198328524369547868622608052551673978575827859267420718) * 10 ^ 70 +
        2675766360193954204785699007036731769286616446963641443847640264326184) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 27 +
      175 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 93,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 176,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (326 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_326 :
    recurrence2Scalar1Main.coeff 326 =
      -(((3936890612143167948971256628318076 * 10 ^ 70 +
        4706339461649136878754081761776680222139649022052138805994501496260607) * 10 ^ 70 +
        2790666993899646794605374926074523382688717635715000933914965675091938) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 26 +
      176 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 94,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 177,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (327 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_327 :
    recurrence2Scalar1Main.coeff 327 =
      (((292315402242204107613833580340204 * 10 ^ 70 +
        1529040197843110998902876566100975016346945782070937806200036431516969) * 10 ^ 70 +
        8649507349264886326169926502411498378625200508757508907356366055802988) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 25 +
      177 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 95,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 178,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (328 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_328 :
    recurrence2Scalar1Main.coeff 328 =
      -(((11425722820211379679141625522393 * 10 ^ 70 +
        1671994518725692671475468407507195143068780952594004234855928347298899) * 10 ^ 70 +
        6752150441232572056246642245491235610527873509412131936900669440079399) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 24 +
      178 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 96,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 179,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (329 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_329 :
    recurrence2Scalar1Main.coeff 329 =
      -(((498823343028814528334612098291 * 10 ^ 70 +
        8545009951455842001652544408366333115085813416447909635984951922500078) * 10 ^ 70 +
        4871201852222330035791297604368267784298295410369168552247740884660316) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 23 +
      179 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 97,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 180,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (330 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_330 :
    recurrence2Scalar1Main.coeff 330 =
      (((135644591992779898368916662093 * 10 ^ 70 +
        6919506516512777901180375414370370650590976872750234051797274451269754) * 10 ^ 70 +
        2439708364340796362718439604385167888297082022745955043048619761522488) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 22 +
      180 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 98,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 181,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (331 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_331 :
    recurrence2Scalar1Main.coeff 331 =
      -(((13497670761367856140509916329 * 10 ^ 70 +
        1271617766690670024868536899921931608193757847466653480645282265438183) * 10 ^ 70 +
        4091012170048961823766732508272179486033708679855994398163704338110878) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 21 +
      181 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 99,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 182,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (332 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_332 :
    recurrence2Scalar1Main.coeff 332 =
      (((846369700333953928080638897 * 10 ^ 70 +
        3954111931563334943116072691116763339143695212180520944327074338203072) * 10 ^ 70 +
        8815169096384878786120898254597894243582408101090500869176377826083924) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 20 +
      182 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 100,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 183,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (333 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_333 :
    recurrence2Scalar1Main.coeff 333 =
      -(((30337230249787186777241050 * 10 ^ 70 +
        5740050030174702955203262693385133802548956640029672225857572957978853) * 10 ^ 70 +
        7104637694985004104758976958641751558806718651430656491238930966443927) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 19 +
      183 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 101,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 184,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (334 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_334 :
    recurrence2Scalar1Main.coeff 334 =
      -(((200901537136208063037858 * 10 ^ 70 +
        8647040227816484471691585714657020061684633771248356773251331529986035) * 10 ^ 70 +
        1636294667682527947518357866611960632540366283649953612094813260870897) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 18 +
      184 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 102,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 185,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (335 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_335 :
    recurrence2Scalar1Main.coeff 335 =
      (((111807098803629991193069 * 10 ^ 70 +
        5415019703961389331742780602797157827891287531048340564653419436100415) * 10 ^ 70 +
        9230882154840539868289169726868362079060136590497488743098647703976246) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 17 +
      185 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 103,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 186,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (336 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_336 :
    recurrence2Scalar1Main.coeff 336 =
      -(((8283592157090366967221 * 10 ^ 70 +
        3981555187239525042621952510612727754869659605164310575820582853654060) * 10 ^ 70 +
        0782272592265814375073648172117586101784273351350983604788386231458565) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 16 +
      186 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 104,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 187,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (337 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_337 :
    recurrence2Scalar1Main.coeff 337 =
      (((341252410607635173671 * 10 ^ 70 +
        5071741101327398071876430080521340359944885857146440339137630983564310) * 10 ^ 70 +
        0559286373056440730989116705452546347416535622808610970268489008946840) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 15 +
      187 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 105,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 188,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (338 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_338 :
    recurrence2Scalar1Main.coeff 338 =
      -(((6420915478082712553 * 10 ^ 70 +
        6602964471544151177256431182684673636592656703620292916704035137067886) * 10 ^ 70 +
        4071726221715339578635237074351247719987411171617243214144582403126640) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 14 +
      188 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 106,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 189,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (339 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_339 :
    recurrence2Scalar1Main.coeff 339 =
      -(((159406125514948132 * 10 ^ 70 +
        6199001439124501867759353404754330637371014547048124980443077299915802) * 10 ^ 70 +
        8886484717254362361506721606399045853294668099640834729603411111082112) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 13 +
      189 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
