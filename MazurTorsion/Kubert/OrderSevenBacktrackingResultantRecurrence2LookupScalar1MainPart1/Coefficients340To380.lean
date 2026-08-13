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

private theorem recurrence2Scalar1Main_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 107,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 190,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (340 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_340 :
    recurrence2Scalar1Main.coeff 340 =
      (((16154575075469365 * 10 ^ 70 +
        2228682994987135847944285400966312830082717888924584770544885523542532) * 10 ^ 70 +
        6631576097808685093232751989779412271728578154236717476722185171187422) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 12 +
      190 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 108,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 191,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (341 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_341 :
    recurrence2Scalar1Main.coeff 341 =
      -(((552125512152198 * 10 ^ 70 +
        6828820917938830733347366309051706973636324520926287369373836536677723) * 10 ^ 70 +
        7425956892736931283297490866174833231883994130086010613883094429152166) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 11 +
      191 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 109,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 192,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (342 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_342 :
    recurrence2Scalar1Main.coeff 342 =
      (((7998929798936 * 10 ^ 70 +
        2524725959550727756273989685947478394325490081250532286585730582422724) * 10 ^ 70 +
        7710498554034662541223639863663337474839996311505638577313859743842960) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 10 +
      192 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 110,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 193,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (343 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_343 :
    recurrence2Scalar1Main.coeff 343 =
      (((92716453860 * 10 ^ 70 +
        6992172571158352268101914206185175833002624392450396335916917816096830) * 10 ^ 70 +
        7802852383615195284179027213981968318584849339393464789089977114200152) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 9 +
      193 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 111,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 194,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (344 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_344 :
    recurrence2Scalar1Main.coeff 344 =
      -(((6594252969 * 10 ^ 70 +
        2216330010067704917700606199570515634832734475427076637151608351255612) * 10 ^ 70 +
        0221679668780823104016343794705205830671124678634719314287675065062241) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 8 +
      194 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 112,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 195,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (345 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_345 :
    recurrence2Scalar1Main.coeff 345 =
      (((116913337 * 10 ^ 70 +
        7430987339465572828146556615369847657037042834573213915605770684407981) * 10 ^ 70 +
        4893304609478257444858399544171137427262514385342593641927718635723381) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 7 +
      195 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 113,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 196,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (346 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_346 :
    recurrence2Scalar1Main.coeff 346 =
      -(((277613 * 10 ^ 70 +
        4289575186621364036903975412626874430117967108040097601326946040588895) * 10 ^ 70 +
        7180662390707937610061674275453688339996065784108715116653969555142948) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 6 +
      196 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 114,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 197,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (347 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_347 :
    recurrence2Scalar1Main.coeff 347 =
      -(((21726 * 10 ^ 70 +
        4500067162658006953240212662583719943152870625018446763880003191690086) * 10 ^ 70 +
        8205421186641873738385901997200806067918050315470664246706108292313476) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 5 +
      197 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 115,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 198,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (348 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_348 :
    recurrence2Scalar1Main.coeff 348 =
      (((305 * 10 ^ 70 +
        3285976192977904300165054967579245300920150102144102160418249779142034) * 10 ^ 70 +
        5981868798345560033861522135672042578464622260214900621860965441052939) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 4 +
      198 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 116,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 199,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (349 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_349 :
    recurrence2Scalar1Main.coeff 349 =
      -((255023266462677687949570533108224831433359340567343516724690958280458 * 10 ^ 70 +
        0501692446628863974561248068471376409520406390648765141364615653803564) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 3 +
      199 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 117,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 200,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (350 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_350 :
    recurrence2Scalar1Main.coeff 350 =
      -((299304685398778295525225438762974471459629214395928440869661364241656 * 10 ^ 70 +
        8837975700467144115851499940305453607984085061141144145097173347842733) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 2 +
      200 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 118,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 201,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (351 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_351 :
    recurrence2Scalar1Main.coeff 351 =
      ((1607212397546147470277788975821157583447943226946169064288850895769 * 10 ^ 70 +
        3150609636485080074440558144045711475798200163920292707800797951284393) : ℚ) := by
  unfold recurrence2Scalar1Main
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
    rw [show 202 = 1 +
      201 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 119,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 202,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (352 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_352 :
    recurrence2Scalar1Main.coeff 352 =
      ((11532797458167162029950568694302783251446793038655386277153441426 * 10 ^ 70 +
        8243928610604246836844156406693159650618174140219949167514507100756040) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 119 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 120,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 203,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (353 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_353 :
    recurrence2Scalar1Main.coeff 353 =
      -((111921552642742853904359172789813822888825730909825745820892112 * 10 ^ 70 +
        6578904562340013700008481459594040907359746494392871473143715315805234) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 120 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 31 +
      203 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 121,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 204,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (354 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_354 :
    recurrence2Scalar1Main.coeff 354 =
      -((153276986337063196275532505656109961948938233999288230872568 * 10 ^ 70 +
        2542983311637004514584377648345849766729737831804470686208559313750161) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 121 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 30 +
      204 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 122,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 205,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (355 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_355 :
    recurrence2Scalar1Main.coeff 355 =
      ((3558662190064658618160194758910578976744361229343438657262 * 10 ^ 70 +
        2563258465426575088084156715024279927997483246423985115924995481787132) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 122 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 29 +
      205 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 123,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 206,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (356 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_356 :
    recurrence2Scalar1Main.coeff 356 =
      -((2468590183060302174674969455162366468680161395885404269 * 10 ^ 70 +
        4234955954580544312370749889911665660849827216188559269378285888227479) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 123 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 28 +
      206 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 124,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 207,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (357 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_357 :
    recurrence2Scalar1Main.coeff 357 =
      -((60204690331842834994209773787725476393871423790111855 * 10 ^ 70 +
        3985099978084661859588765477417015370495342924707826389143195883482637) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 124 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 27 +
      207 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 125,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 208,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (358 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_358 :
    recurrence2Scalar1Main.coeff 358 =
      ((117392116005878349529302266062121015888140109148494 * 10 ^ 70 +
        7055470987409052949433853256871688485155665203848211975063122826277902) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 125 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 26 +
      208 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 126,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 209,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (359 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_359 :
    recurrence2Scalar1Main.coeff 359 =
      ((514021931773066408557419041919426281797503412351 * 10 ^ 70 +
        4463339835268052188805937361325208477632930418349155352034599891665059) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 126 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 25 +
      209 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 127,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 210,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (360 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_360 :
    recurrence2Scalar1Main.coeff 360 =
      -((1688319288914077861132209179289751178695044690 * 10 ^ 70 +
        9209085032029179976703412396123178384606214812306845697959499849222874) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 127 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 24 +
      210 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 128,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 211,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (361 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_361 :
    recurrence2Scalar1Main.coeff 361 =
      -((1324371976306264655164873305221428035148249 * 10 ^ 70 +
        7404923124811930019725713068494866019129331433321020147256721786059729) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 128 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 23 +
      211 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 129,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 212,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (362 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_362 :
    recurrence2Scalar1Main.coeff 362 =
      ((10636030761453979689212503384152804234955 * 10 ^ 70 +
        1854415116944574989769725640984161092963918075211170545258342029886627) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 129 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 22 +
      212 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 130,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 213,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (363 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_363 :
    recurrence2Scalar1Main.coeff 363 =
      -((8537176014618503039291488575504032301 * 10 ^ 70 +
        5124643929346089275027784188248228410358163040784307271925987716495935) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 130 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 21 +
      213 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 131,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 214,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (364 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_364 :
    recurrence2Scalar1Main.coeff 364 =
      -((20833364884807867081566465475813569 * 10 ^ 70 +
        5502539424804837572628025700237095345319074065533007791695181376533682) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 131 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 20 +
      214 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 132,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 215,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (365 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_365 :
    recurrence2Scalar1Main.coeff 365 =
      ((45344066302479503706069207564273 * 10 ^ 70 +
        5938408589883540422755543450498130755547636781994440523780186208360983) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 132 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 19 +
      215 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 133,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 216,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (366 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_366 :
    recurrence2Scalar1Main.coeff 366 =
      -((26348654263148535796765589022 * 10 ^ 70 +
        8596372241128746551227296579203451412166228351078043082486294803759525) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 133 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 18 +
      216 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 134,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 217,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (367 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_367 :
    recurrence2Scalar1Main.coeff 367 =
      -((8794114326128746361480533 * 10 ^ 70 +
        9636358131368919596620743056425236604937436377444990320864026851288284) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 134 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 17 +
      217 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 135,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 218,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (368 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_368 :
    recurrence2Scalar1Main.coeff 368 =
      ((17524038748515487788193 * 10 ^ 70 +
        9950650506267910206229009464758802755798660615509707504223275025334442) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 135 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 16 +
      218 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 136,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 219,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (369 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_369 :
    recurrence2Scalar1Main.coeff 369 =
      -((7820265960553442480 * 10 ^ 70 +
        8147063015890297590954470001783686516431444126262720346787777153371130) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 136 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 15 +
      219 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 137,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 220,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (370 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_370 :
    recurrence2Scalar1Main.coeff 370 =
      ((1284062138148437 * 10 ^ 70 +
        2937172338891122596482251604224861175591479805839106153108802119817096) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 137 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 14 +
      220 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 138,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 221,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (371 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_371 :
    recurrence2Scalar1Main.coeff 371 =
      ((6056773305 * 10 ^ 70 +
        4376143428844497661836083984271269543245720365111271753577841060401837) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 138 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 13 +
      221 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 139,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 222,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (372 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_372 :
    recurrence2Scalar1Main.coeff 372 =
      -((21730737 * 10 ^ 70 +
        8368203681559182759958593108605614464334983719335070636208312972429622) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 139 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 12 +
      222 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 140,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 223,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (373 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_373 :
    recurrence2Scalar1Main.coeff 373 =
      ((1971 * 10 ^ 70 +
        6412474866066035204641552036575141170616240814378935948130652802991478) : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 140 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 11 +
      223 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 141,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 224,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (374 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_374 :
    recurrence2Scalar1Main.coeff 374 =
      (-572606090269610926200079869496753797698513187349143131732852629980405 : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 141 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 10 +
      224 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 142,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 225,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (375 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_375 :
    recurrence2Scalar1Main.coeff 375 =
      (4538895923742927442863247914666917054513848007748787677190147260 : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 142 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 9 +
      225 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 143,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 226,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (376 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_376 :
    recurrence2Scalar1Main.coeff 376 =
      (27254968769581522096998684086205648522251257357628257996792 : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 143 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 8 +
      226 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 144,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 227,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (377 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_377 :
    recurrence2Scalar1Main.coeff 377 =
      (-265319237024263686274044497625793639446160394747550923 : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 144 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 7 +
      227 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 145,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 228,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (378 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_378 :
    recurrence2Scalar1Main.coeff 378 =
      (500649091397656411914350428601274543111479793877 : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 379 = 145 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 6 +
      228 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 146,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 229,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (379 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_379 :
    recurrence2Scalar1Main.coeff 379 =
      (-137363268378719150678779313362487539087671 : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 380 = 146 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 5 +
      229 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Main_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 147,
      remainder3Coefficient1.coeff x * recurrence2QuotientConstant.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2QuotientConstant_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Main_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 230,
      remainder3Coefficient1.coeff (151 + x) *
        recurrence2QuotientConstant.coeff (380 - (151 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2B1_coeff_high (151 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Main_coeff_380 :
    recurrence2Scalar1Main.coeff 380 =
      (7643129673958697547995641780269088 : ℚ) := by
  unfold recurrence2Scalar1Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 381 = 147 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 4 +
      230 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Main_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Main_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
