/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C1_coeff_1
  recurrence4C1_coeff_10
  recurrence4C1_coeff_100
  recurrence4C1_coeff_101
  recurrence4C1_coeff_102
  recurrence4C1_coeff_103
  recurrence4C1_coeff_104
  recurrence4C1_coeff_105
  recurrence4C1_coeff_106
  recurrence4C1_coeff_107
  recurrence4C1_coeff_108
  recurrence4C1_coeff_109
  recurrence4C1_coeff_11
  recurrence4C1_coeff_110
  recurrence4C1_coeff_111
  recurrence4C1_coeff_112
  recurrence4C1_coeff_113
  recurrence4C1_coeff_114
  recurrence4C1_coeff_115
  recurrence4C1_coeff_116
  recurrence4C1_coeff_117
  recurrence4C1_coeff_118
  recurrence4C1_coeff_119
  recurrence4C1_coeff_12
  recurrence4C1_coeff_120
  recurrence4C1_coeff_121
  recurrence4C1_coeff_122
  recurrence4C1_coeff_123
  recurrence4C1_coeff_124
  recurrence4C1_coeff_125
  recurrence4C1_coeff_126
  recurrence4C1_coeff_127
  recurrence4C1_coeff_128
  recurrence4C1_coeff_129
  recurrence4C1_coeff_13
  recurrence4C1_coeff_130
  recurrence4C1_coeff_131
  recurrence4C1_coeff_132
  recurrence4C1_coeff_133
  recurrence4C1_coeff_134
  recurrence4C1_coeff_135
  recurrence4C1_coeff_136
  recurrence4C1_coeff_137
  recurrence4C1_coeff_138
  recurrence4C1_coeff_139
  recurrence4C1_coeff_14
  recurrence4C1_coeff_140
  recurrence4C1_coeff_141
  recurrence4C1_coeff_142
  recurrence4C1_coeff_143
  recurrence4C1_coeff_144
  recurrence4C1_coeff_145
  recurrence4C1_coeff_146
  recurrence4C1_coeff_147
  recurrence4C1_coeff_148
  recurrence4C1_coeff_149
  recurrence4C1_coeff_15
  recurrence4C1_coeff_16
  recurrence4C1_coeff_17
  recurrence4C1_coeff_18
  recurrence4C1_coeff_19
  recurrence4C1_coeff_2
  recurrence4C1_coeff_20
  recurrence4C1_coeff_21

attribute [local simp]
  recurrence4C1_coeff_22
  recurrence4C1_coeff_23
  recurrence4C1_coeff_24
  recurrence4C1_coeff_25
  recurrence4C1_coeff_26
  recurrence4C1_coeff_27
  recurrence4C1_coeff_28
  recurrence4C1_coeff_29
  recurrence4C1_coeff_3
  recurrence4C1_coeff_30
  recurrence4C1_coeff_31
  recurrence4C1_coeff_32
  recurrence4C1_coeff_33
  recurrence4C1_coeff_34
  recurrence4C1_coeff_35
  recurrence4C1_coeff_36
  recurrence4C1_coeff_37
  recurrence4C1_coeff_38
  recurrence4C1_coeff_39
  recurrence4C1_coeff_4
  recurrence4C1_coeff_40
  recurrence4C1_coeff_41
  recurrence4C1_coeff_42
  recurrence4C1_coeff_43
  recurrence4C1_coeff_44
  recurrence4C1_coeff_45
  recurrence4C1_coeff_46
  recurrence4C1_coeff_47
  recurrence4C1_coeff_48
  recurrence4C1_coeff_49
  recurrence4C1_coeff_5
  recurrence4C1_coeff_50
  recurrence4C1_coeff_51
  recurrence4C1_coeff_52
  recurrence4C1_coeff_53
  recurrence4C1_coeff_54
  recurrence4C1_coeff_55
  recurrence4C1_coeff_56
  recurrence4C1_coeff_57
  recurrence4C1_coeff_58
  recurrence4C1_coeff_59
  recurrence4C1_coeff_6
  recurrence4C1_coeff_60
  recurrence4C1_coeff_61
  recurrence4C1_coeff_62
  recurrence4C1_coeff_63
  recurrence4C1_coeff_64
  recurrence4C1_coeff_65
  recurrence4C1_coeff_66
  recurrence4C1_coeff_67
  recurrence4C1_coeff_68
  recurrence4C1_coeff_69
  recurrence4C1_coeff_7
  recurrence4C1_coeff_70
  recurrence4C1_coeff_71
  recurrence4C1_coeff_72
  recurrence4C1_coeff_73
  recurrence4C1_coeff_74
  recurrence4C1_coeff_75
  recurrence4C1_coeff_76
  recurrence4C1_coeff_77
  recurrence4C1_coeff_78
  recurrence4C1_coeff_79
  recurrence4C1_coeff_8

attribute [local simp]
  recurrence4C1_coeff_80
  recurrence4C1_coeff_81
  recurrence4C1_coeff_82
  recurrence4C1_coeff_83
  recurrence4C1_coeff_84
  recurrence4C1_coeff_85
  recurrence4C1_coeff_86
  recurrence4C1_coeff_87
  recurrence4C1_coeff_88
  recurrence4C1_coeff_89
  recurrence4C1_coeff_9
  recurrence4C1_coeff_90
  recurrence4C1_coeff_91
  recurrence4C1_coeff_92
  recurrence4C1_coeff_93
  recurrence4C1_coeff_94
  recurrence4C1_coeff_95
  recurrence4C1_coeff_96
  recurrence4C1_coeff_97
  recurrence4C1_coeff_98
  recurrence4C1_coeff_99
  recurrence4ExceptionalProduct_coeff_100
  recurrence4ExceptionalProduct_coeff_101
  recurrence4ExceptionalProduct_coeff_102
  recurrence4ExceptionalProduct_coeff_103
  recurrence4ExceptionalProduct_coeff_104
  recurrence4ExceptionalProduct_coeff_105
  recurrence4ExceptionalProduct_coeff_106
  recurrence4ExceptionalProduct_coeff_107
  recurrence4ExceptionalProduct_coeff_108
  recurrence4ExceptionalProduct_coeff_109
  recurrence4ExceptionalProduct_coeff_110
  recurrence4ExceptionalProduct_coeff_111
  recurrence4ExceptionalProduct_coeff_112
  recurrence4ExceptionalProduct_coeff_113
  recurrence4ExceptionalProduct_coeff_114
  recurrence4ExceptionalProduct_coeff_115
  recurrence4ExceptionalProduct_coeff_116
  recurrence4ExceptionalProduct_coeff_117
  recurrence4ExceptionalProduct_coeff_118
  recurrence4ExceptionalProduct_coeff_119
  recurrence4ExceptionalProduct_coeff_12
  recurrence4ExceptionalProduct_coeff_120
  recurrence4ExceptionalProduct_coeff_121
  recurrence4ExceptionalProduct_coeff_122
  recurrence4ExceptionalProduct_coeff_123
  recurrence4ExceptionalProduct_coeff_124
  recurrence4ExceptionalProduct_coeff_125
  recurrence4ExceptionalProduct_coeff_126
  recurrence4ExceptionalProduct_coeff_127
  recurrence4ExceptionalProduct_coeff_128
  recurrence4ExceptionalProduct_coeff_129
  recurrence4ExceptionalProduct_coeff_13
  recurrence4ExceptionalProduct_coeff_130
  recurrence4ExceptionalProduct_coeff_131
  recurrence4ExceptionalProduct_coeff_132
  recurrence4ExceptionalProduct_coeff_133
  recurrence4ExceptionalProduct_coeff_134
  recurrence4ExceptionalProduct_coeff_135
  recurrence4ExceptionalProduct_coeff_136
  recurrence4ExceptionalProduct_coeff_137
  recurrence4ExceptionalProduct_coeff_138
  recurrence4ExceptionalProduct_coeff_139
  recurrence4ExceptionalProduct_coeff_14

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_140
  recurrence4ExceptionalProduct_coeff_141
  recurrence4ExceptionalProduct_coeff_142
  recurrence4ExceptionalProduct_coeff_143
  recurrence4ExceptionalProduct_coeff_144
  recurrence4ExceptionalProduct_coeff_145
  recurrence4ExceptionalProduct_coeff_146
  recurrence4ExceptionalProduct_coeff_147
  recurrence4ExceptionalProduct_coeff_148
  recurrence4ExceptionalProduct_coeff_149
  recurrence4ExceptionalProduct_coeff_15
  recurrence4ExceptionalProduct_coeff_150
  recurrence4ExceptionalProduct_coeff_151
  recurrence4ExceptionalProduct_coeff_152
  recurrence4ExceptionalProduct_coeff_153
  recurrence4ExceptionalProduct_coeff_154
  recurrence4ExceptionalProduct_coeff_155
  recurrence4ExceptionalProduct_coeff_156
  recurrence4ExceptionalProduct_coeff_157
  recurrence4ExceptionalProduct_coeff_158
  recurrence4ExceptionalProduct_coeff_159
  recurrence4ExceptionalProduct_coeff_16
  recurrence4ExceptionalProduct_coeff_160
  recurrence4ExceptionalProduct_coeff_161
  recurrence4ExceptionalProduct_coeff_162
  recurrence4ExceptionalProduct_coeff_163
  recurrence4ExceptionalProduct_coeff_164
  recurrence4ExceptionalProduct_coeff_165
  recurrence4ExceptionalProduct_coeff_166
  recurrence4ExceptionalProduct_coeff_167
  recurrence4ExceptionalProduct_coeff_168
  recurrence4ExceptionalProduct_coeff_169
  recurrence4ExceptionalProduct_coeff_17
  recurrence4ExceptionalProduct_coeff_170
  recurrence4ExceptionalProduct_coeff_171
  recurrence4ExceptionalProduct_coeff_172
  recurrence4ExceptionalProduct_coeff_173
  recurrence4ExceptionalProduct_coeff_174
  recurrence4ExceptionalProduct_coeff_175
  recurrence4ExceptionalProduct_coeff_176
  recurrence4ExceptionalProduct_coeff_177
  recurrence4ExceptionalProduct_coeff_178
  recurrence4ExceptionalProduct_coeff_179
  recurrence4ExceptionalProduct_coeff_18
  recurrence4ExceptionalProduct_coeff_180
  recurrence4ExceptionalProduct_coeff_181
  recurrence4ExceptionalProduct_coeff_182
  recurrence4ExceptionalProduct_coeff_183
  recurrence4ExceptionalProduct_coeff_184
  recurrence4ExceptionalProduct_coeff_185
  recurrence4ExceptionalProduct_coeff_186
  recurrence4ExceptionalProduct_coeff_187
  recurrence4ExceptionalProduct_coeff_188
  recurrence4ExceptionalProduct_coeff_189
  recurrence4ExceptionalProduct_coeff_19
  recurrence4ExceptionalProduct_coeff_190
  recurrence4ExceptionalProduct_coeff_191
  recurrence4ExceptionalProduct_coeff_192
  recurrence4ExceptionalProduct_coeff_193
  recurrence4ExceptionalProduct_coeff_194
  recurrence4ExceptionalProduct_coeff_195
  recurrence4ExceptionalProduct_coeff_196
  recurrence4ExceptionalProduct_coeff_197
  recurrence4ExceptionalProduct_coeff_198

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_199
  recurrence4ExceptionalProduct_coeff_20
  recurrence4ExceptionalProduct_coeff_200
  recurrence4ExceptionalProduct_coeff_201
  recurrence4ExceptionalProduct_coeff_202
  recurrence4ExceptionalProduct_coeff_203
  recurrence4ExceptionalProduct_coeff_204
  recurrence4ExceptionalProduct_coeff_205
  recurrence4ExceptionalProduct_coeff_206
  recurrence4ExceptionalProduct_coeff_207
  recurrence4ExceptionalProduct_coeff_208
  recurrence4ExceptionalProduct_coeff_209
  recurrence4ExceptionalProduct_coeff_21
  recurrence4ExceptionalProduct_coeff_210
  recurrence4ExceptionalProduct_coeff_211
  recurrence4ExceptionalProduct_coeff_212
  recurrence4ExceptionalProduct_coeff_213
  recurrence4ExceptionalProduct_coeff_214
  recurrence4ExceptionalProduct_coeff_215
  recurrence4ExceptionalProduct_coeff_216
  recurrence4ExceptionalProduct_coeff_217
  recurrence4ExceptionalProduct_coeff_218
  recurrence4ExceptionalProduct_coeff_219
  recurrence4ExceptionalProduct_coeff_22
  recurrence4ExceptionalProduct_coeff_220
  recurrence4ExceptionalProduct_coeff_221
  recurrence4ExceptionalProduct_coeff_222
  recurrence4ExceptionalProduct_coeff_223
  recurrence4ExceptionalProduct_coeff_224
  recurrence4ExceptionalProduct_coeff_225
  recurrence4ExceptionalProduct_coeff_226
  recurrence4ExceptionalProduct_coeff_227
  recurrence4ExceptionalProduct_coeff_228
  recurrence4ExceptionalProduct_coeff_229
  recurrence4ExceptionalProduct_coeff_23
  recurrence4ExceptionalProduct_coeff_230
  recurrence4ExceptionalProduct_coeff_231
  recurrence4ExceptionalProduct_coeff_232
  recurrence4ExceptionalProduct_coeff_233
  recurrence4ExceptionalProduct_coeff_234
  recurrence4ExceptionalProduct_coeff_235
  recurrence4ExceptionalProduct_coeff_236
  recurrence4ExceptionalProduct_coeff_237
  recurrence4ExceptionalProduct_coeff_238
  recurrence4ExceptionalProduct_coeff_239
  recurrence4ExceptionalProduct_coeff_24
  recurrence4ExceptionalProduct_coeff_240
  recurrence4ExceptionalProduct_coeff_241
  recurrence4ExceptionalProduct_coeff_242
  recurrence4ExceptionalProduct_coeff_243
  recurrence4ExceptionalProduct_coeff_244
  recurrence4ExceptionalProduct_coeff_245
  recurrence4ExceptionalProduct_coeff_246
  recurrence4ExceptionalProduct_coeff_247
  recurrence4ExceptionalProduct_coeff_248
  recurrence4ExceptionalProduct_coeff_249
  recurrence4ExceptionalProduct_coeff_25
  recurrence4ExceptionalProduct_coeff_250
  recurrence4ExceptionalProduct_coeff_251
  recurrence4ExceptionalProduct_coeff_252
  recurrence4ExceptionalProduct_coeff_253
  recurrence4ExceptionalProduct_coeff_254
  recurrence4ExceptionalProduct_coeff_255
  recurrence4ExceptionalProduct_coeff_256

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_257
  recurrence4ExceptionalProduct_coeff_258
  recurrence4ExceptionalProduct_coeff_259
  recurrence4ExceptionalProduct_coeff_26
  recurrence4ExceptionalProduct_coeff_260
  recurrence4ExceptionalProduct_coeff_261
  recurrence4ExceptionalProduct_coeff_262
  recurrence4ExceptionalProduct_coeff_263
  recurrence4ExceptionalProduct_coeff_264
  recurrence4ExceptionalProduct_coeff_265
  recurrence4ExceptionalProduct_coeff_266
  recurrence4ExceptionalProduct_coeff_267
  recurrence4ExceptionalProduct_coeff_268
  recurrence4ExceptionalProduct_coeff_269
  recurrence4ExceptionalProduct_coeff_27
  recurrence4ExceptionalProduct_coeff_270
  recurrence4ExceptionalProduct_coeff_28
  recurrence4ExceptionalProduct_coeff_29
  recurrence4ExceptionalProduct_coeff_30
  recurrence4ExceptionalProduct_coeff_31
  recurrence4ExceptionalProduct_coeff_32
  recurrence4ExceptionalProduct_coeff_33
  recurrence4ExceptionalProduct_coeff_34
  recurrence4ExceptionalProduct_coeff_35
  recurrence4ExceptionalProduct_coeff_36
  recurrence4ExceptionalProduct_coeff_37
  recurrence4ExceptionalProduct_coeff_38
  recurrence4ExceptionalProduct_coeff_39
  recurrence4ExceptionalProduct_coeff_40
  recurrence4ExceptionalProduct_coeff_41
  recurrence4ExceptionalProduct_coeff_42
  recurrence4ExceptionalProduct_coeff_43
  recurrence4ExceptionalProduct_coeff_44
  recurrence4ExceptionalProduct_coeff_45
  recurrence4ExceptionalProduct_coeff_46
  recurrence4ExceptionalProduct_coeff_47
  recurrence4ExceptionalProduct_coeff_48
  recurrence4ExceptionalProduct_coeff_49
  recurrence4ExceptionalProduct_coeff_50
  recurrence4ExceptionalProduct_coeff_51
  recurrence4ExceptionalProduct_coeff_52
  recurrence4ExceptionalProduct_coeff_53
  recurrence4ExceptionalProduct_coeff_54
  recurrence4ExceptionalProduct_coeff_55
  recurrence4ExceptionalProduct_coeff_56
  recurrence4ExceptionalProduct_coeff_57
  recurrence4ExceptionalProduct_coeff_58
  recurrence4ExceptionalProduct_coeff_59
  recurrence4ExceptionalProduct_coeff_60
  recurrence4ExceptionalProduct_coeff_61
  recurrence4ExceptionalProduct_coeff_62
  recurrence4ExceptionalProduct_coeff_63
  recurrence4ExceptionalProduct_coeff_64
  recurrence4ExceptionalProduct_coeff_65
  recurrence4ExceptionalProduct_coeff_66
  recurrence4ExceptionalProduct_coeff_67
  recurrence4ExceptionalProduct_coeff_68
  recurrence4ExceptionalProduct_coeff_69
  recurrence4ExceptionalProduct_coeff_70
  recurrence4ExceptionalProduct_coeff_71
  recurrence4ExceptionalProduct_coeff_72
  recurrence4ExceptionalProduct_coeff_73
  recurrence4ExceptionalProduct_coeff_74
  recurrence4ExceptionalProduct_coeff_75

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_76
  recurrence4ExceptionalProduct_coeff_77
  recurrence4ExceptionalProduct_coeff_78
  recurrence4ExceptionalProduct_coeff_79
  recurrence4ExceptionalProduct_coeff_80
  recurrence4ExceptionalProduct_coeff_81
  recurrence4ExceptionalProduct_coeff_82
  recurrence4ExceptionalProduct_coeff_83
  recurrence4ExceptionalProduct_coeff_84
  recurrence4ExceptionalProduct_coeff_85
  recurrence4ExceptionalProduct_coeff_86
  recurrence4ExceptionalProduct_coeff_87
  recurrence4ExceptionalProduct_coeff_88
  recurrence4ExceptionalProduct_coeff_89
  recurrence4ExceptionalProduct_coeff_90
  recurrence4ExceptionalProduct_coeff_91
  recurrence4ExceptionalProduct_coeff_92
  recurrence4ExceptionalProduct_coeff_93
  recurrence4ExceptionalProduct_coeff_94
  recurrence4ExceptionalProduct_coeff_95
  recurrence4ExceptionalProduct_coeff_96
  recurrence4ExceptionalProduct_coeff_97
  recurrence4ExceptionalProduct_coeff_98
  recurrence4ExceptionalProduct_coeff_99

private theorem recurrence4Scalar1Exceptional_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (250 + x) *
        remainder6Coefficient1.coeff (250 - (250 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 250 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (250 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (250 - (250 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_250 :
    recurrence4Scalar1Exceptional.coeff 250 =
      (((((7012890036652317745723994936 * 10 ^ 70 +
        0585210592432152320510553259264164936190404310955280635819675800659541) * 10 ^ 70 +
        5379208991614919027258339135285285533411994603419397217221111537539873) * 10 ^ 70 +
        4825097338210869732316295130418773426561583326620910693789716444480495) * 10 ^ 70 +
        8997888719510164534354287195007994957318800359744851964654238068683543) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (250 - x)) = _
  rw [show 251 = 101 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (251 + x) *
        remainder6Coefficient1.coeff (251 - (251 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 251 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (251 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (251 - (251 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_251 :
    recurrence4Scalar1Exceptional.coeff 251 =
      -(((((7726929512691935423187376687 * 10 ^ 70 +
        9425944222654309271364703448771244008915128784194300105210296369600332) * 10 ^ 70 +
        8169285416370031137722451456372041558553528268335005722058166823426904) * 10 ^ 70 +
        4050194347523662958866922451164840044896393564158823941312872168921150) * 10 ^ 70 +
        4589358729622065396946564053923095344197014080178745152112843775419290) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (251 - x)) = _
  rw [show 252 = 102 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_251_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (252 + x) *
        remainder6Coefficient1.coeff (252 - (252 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 252 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (252 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (252 - (252 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_252 :
    recurrence4Scalar1Exceptional.coeff 252 =
      (((((8403239344604566741777159198 * 10 ^ 70 +
        8924996328445706539943824642475778780248462517223997365693649506825316) * 10 ^ 70 +
        5718195425692372419306948433139041178419094503633860215119673811888842) * 10 ^ 70 +
        5731712992086450273457470815168540962135893774463969304838052364516927) * 10 ^ 70 +
        1725528998061128053578512805051113766557470839441276741112970331005416) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (252 - x)) = _
  rw [show 253 = 103 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_252_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (253 + x) *
        remainder6Coefficient1.coeff (253 - (253 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 253 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (253 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (253 - (253 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_253 :
    recurrence4Scalar1Exceptional.coeff 253 =
      -(((((9020231246741759949419129660 * 10 ^ 70 +
        4206957521312352680183611017871964091144706582931366478057922510741800) * 10 ^ 70 +
        9509145292209966055920847504597160809459108004783680287642404422950843) * 10 ^ 70 +
        9055519775772253484303283835498146171978944914663520005628846086203798) * 10 ^ 70 +
        0266861273973932692084886362183548303634501978442259036389559762088771) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (253 - x)) = _
  rw [show 254 = 104 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_253_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (254 + x) *
        remainder6Coefficient1.coeff (254 - (254 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 254 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (254 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (254 - (254 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_254 :
    recurrence4Scalar1Exceptional.coeff 254 =
      (((((9556978610277603756472169694 * 10 ^ 70 +
        1621528689735998614766004260632977069340768840002135322291295136704579) * 10 ^ 70 +
        8422127390585853090815955302910895962516044975675326743613983785334549) * 10 ^ 70 +
        6049892418764899739360970871803995917232149527897925296562911009260648) * 10 ^ 70 +
        0574337000629034620466995022495937379398805241961684429431118132795333) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (254 - x)) = _
  rw [show 255 = 105 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_254_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (255 + x) *
        remainder6Coefficient1.coeff (255 - (255 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 255 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (255 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (255 - (255 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_255 :
    recurrence4Scalar1Exceptional.coeff 255 =
      -(((((9994382091225129119404349486 * 10 ^ 70 +
        1226786325249395431966640633145443944799605782478023355418578536119213) * 10 ^ 70 +
        2590269957808719344484057401042861069185378599912205515326384552902137) * 10 ^ 70 +
        4488665992569583776172213810014683008867950179967929455321096430441844) * 10 ^ 70 +
        1836199744004211641216167178038265048856641726850234036676132542758369) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (255 - x)) = _
  rw [show 256 = 106 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_255_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (256 + x) *
        remainder6Coefficient1.coeff (256 - (256 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 256 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (256 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (256 - (256 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_256 :
    recurrence4Scalar1Exceptional.coeff 256 =
      (((((10316290900234845060975604092 * 10 ^ 70 +
        2075650478259523607730080965244548566200240883167056483651452417771961) * 10 ^ 70 +
        6425824922943044354288085404717011748494954983470752044513003633944820) * 10 ^ 70 +
        7485388511582439379940614796584733451626903743031230985706322583208788) * 10 ^ 70 +
        7130941181436944100583173692143816928456235544894662587620818066474169) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (256 - x)) = _
  rw [show 257 = 107 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_256_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (257 + x) *
        remainder6Coefficient1.coeff (257 - (257 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 257 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (257 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (257 - (257 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_257 :
    recurrence4Scalar1Exceptional.coeff 257 =
      -(((((10510488537250681076887195757 * 10 ^ 70 +
        0140214149569360426954915381745305830378483098645139936773719511806214) * 10 ^ 70 +
        8741708481931825051430131332545497741223397549702605604857993579544221) * 10 ^ 70 +
        9548091256317563712252809253472898394383679939429938747538929545735016) * 10 ^ 70 +
        0748974929409768563148505658427989695365381245856071199200018037737752) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (257 - x)) = _
  rw [show 258 = 108 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_257_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (258 + x) *
        remainder6Coefficient1.coeff (258 - (258 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 258 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (258 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (258 - (258 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_258 :
    recurrence4Scalar1Exceptional.coeff 258 =
      (((((10569459388460101510689572141 * 10 ^ 70 +
        1079201100962700198838588211918030568106306541272721328804246360739478) * 10 ^ 70 +
        3421378649916965290031025376552207947980396283587036819753062289452683) * 10 ^ 70 +
        3245465942459096159084395804467420022839217365799724608994491167464889) * 10 ^ 70 +
        6876573805486301128125129117800985913048795856958543254801074796621940) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (258 - x)) = _
  rw [show 259 = 109 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_258_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (259 + x) *
        remainder6Coefficient1.coeff (259 - (259 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 259 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (259 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (259 - (259 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_259 :
    recurrence4Scalar1Exceptional.coeff 259 =
      -(((((10490869323737097095538658491 * 10 ^ 70 +
        7755179716025035163064797137916812161585789270368734052069537754354871) * 10 ^ 70 +
        3841256392585430733515008948173521039157817642910497261854498336500705) * 10 ^ 70 +
        5160400171759331208168467771336107306277831270568122668864061312980231) * 10 ^ 70 +
        6052594432667419846112808855576050044284585710913549738006870711748473) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (259 - x)) = _
  rw [show 260 = 110 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_259_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (260 + x) *
        remainder6Coefficient1.coeff (260 - (260 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 260 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (260 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (260 - (260 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_260 :
    recurrence4Scalar1Exceptional.coeff 260 =
      (((((10277717601643254717104550214 * 10 ^ 70 +
        7458766723092257757216392634992388255500632457920267168632228170036980) * 10 ^ 70 +
        1646389756422678663583637953362385110267425737395643013274577883299437) * 10 ^ 70 +
        0341274254756710050326501523383304122770126136873449724406799268969700) * 10 ^ 70 +
        0938044420338615142905282029791003921133530111915043715179979878124555) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (260 - x)) = _
  rw [show 261 = 111 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_260_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (261 + x) *
        remainder6Coefficient1.coeff (261 - (261 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 261 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (261 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (261 - (261 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_261 :
    recurrence4Scalar1Exceptional.coeff 261 =
      -(((((9938146399936075677558289522 * 10 ^ 70 +
        2931535898165715801305587878012715787975224677639760006705985392924611) * 10 ^ 70 +
        2393885093247395731419299937986140833176009698545114883055705359781335) * 10 ^ 70 +
        2429617146682086988602021673182611471927108544881568991162179856559506) * 10 ^ 70 +
        9717195290335766545236705548534346306134476957365186242673859652946568) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (261 - x)) = _
  rw [show 262 = 112 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_261_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (262 + x) *
        remainder6Coefficient1.coeff (262 - (262 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 262 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (262 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (262 - (262 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_262 :
    recurrence4Scalar1Exceptional.coeff 262 =
      (((((9484924869451202139505674193 * 10 ^ 70 +
        9470981137103519523080557296608106952569149819606937099406033635244234) * 10 ^ 70 +
        6485780345709185675967283407364913636277039432075288198309816631807791) * 10 ^ 70 +
        9753395186884825828246377980262441963049343186293377900994534699791886) * 10 ^ 70 +
        8415987710472943495951572375080657990255174557400249536224371220766770) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (262 - x)) = _
  rw [show 263 = 113 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_262_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (263 + x) *
        remainder6Coefficient1.coeff (263 - (263 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 263 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (263 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (263 - (263 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_263 :
    recurrence4Scalar1Exceptional.coeff 263 =
      -(((((8934653267098201396538498699 * 10 ^ 70 +
        5726595399272374496857985662659972716612512546567781460142341619134033) * 10 ^ 70 +
        3226012731927169817284974306543156943788050762283765122507385103409555) * 10 ^ 70 +
        1087836729032673246949235988073487848629116769427260502394958541812872) * 10 ^ 70 +
        8455377146993082311766759333441883880456653885192676939027029636467528) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (263 - x)) = _
  rw [show 264 = 114 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_263_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (264 + x) *
        remainder6Coefficient1.coeff (264 - (264 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 264 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (264 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (264 - (264 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_264 :
    recurrence4Scalar1Exceptional.coeff 264 =
      (((((8306756234739230678386533230 * 10 ^ 70 +
        0839271547947905373179016407617163341089929749103255524765890590228000) * 10 ^ 70 +
        3374723837352642122820936903486427185991596365210999689554525006471180) * 10 ^ 70 +
        8412111822356736426014601245841472769837579258580279040237876937147420) * 10 ^ 70 +
        3154047811208111405261465049059275740258282374753488260492134043259261) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (264 - x)) = _
  rw [show 265 = 115 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_264_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (265 + x) *
        remainder6Coefficient1.coeff (265 - (265 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 265 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (265 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (265 - (265 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_265 :
    recurrence4Scalar1Exceptional.coeff 265 =
      -(((((7622350137340241330972926874 * 10 ^ 70 +
        6091611455387140070442348160897339948363577538639923501737601404820386) * 10 ^ 70 +
        5857736240059243753129946639632711398550380135841951213020141325923263) * 10 ^ 70 +
        6185925036554787564280181203413177554065606847260521207170627784526122) * 10 ^ 70 +
        6127954604444681576159449252250712679186841392680473391111715733444340) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (265 - x)) = _
  rw [show 266 = 116 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_265_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (266 + x) *
        remainder6Coefficient1.coeff (266 - (266 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 266 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (266 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (266 - (266 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_266 :
    recurrence4Scalar1Exceptional.coeff 266 =
      (((((6903076072337556227442363687 * 10 ^ 70 +
        9973341869425515204765001482174660808709811505679657621083079922255445) * 10 ^ 70 +
        0132400771691725519518113546307099831271066263297660534781974871685855) * 10 ^ 70 +
        4274904918711201395083417934782164361500086070714524095656775097163368) * 10 ^ 70 +
        2581179628800077242215575839869708194005394495412672505640423241564944) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (266 - x)) = _
  rw [show 267 = 117 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_266_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (267 + x) *
        remainder6Coefficient1.coeff (267 - (267 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 267 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (267 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (267 - (267 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_267 :
    recurrence4Scalar1Exceptional.coeff 267 =
      -(((((6169987425635837387353569118 * 10 ^ 70 +
        5890503601918731247943269570526589968715023500788038049336758173080297) * 10 ^ 70 +
        7648368840158301817887306882263045168309932931023615923273334997344443) * 10 ^ 70 +
        0433842216297216288866865759794063496862338367377397144738902734985320) * 10 ^ 70 +
        6874658812467047446785240538564331124050637137372215362116005287571190) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (267 - x)) = _
  rw [show 268 = 118 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_267_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (268 + x) *
        remainder6Coefficient1.coeff (268 - (268 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 268 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (268 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (268 - (268 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_268 :
    recurrence4Scalar1Exceptional.coeff 268 =
      (((((5442569566647864634999277077 * 10 ^ 70 +
        5003313699009596596886366700493745808847609168302030422581048975642651) * 10 ^ 70 +
        2907009048283083983323260061362098795524482647343513646559606755165526) * 10 ^ 70 +
        4033980723941896856074355563642189008846802577698606391966532342476648) * 10 ^ 70 +
        2831423417116313803798486143723503859956406018151880327996793833262537) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (268 - x)) = _
  rw [show 269 = 119 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_268_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (269 + x) *
        remainder6Coefficient1.coeff (269 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 269 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (269 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (269 - (269 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_269 :
    recurrence4Scalar1Exceptional.coeff 269 =
      -(((((4737951317235291980200633154 * 10 ^ 70 +
        6886651909028446041112586228210054537818105759155492550896666196992629) * 10 ^ 70 +
        7124510457731553601724657517667785111540471168335324910421288231250314) * 10 ^ 70 +
        3794539246088381054036640635324179645129940480837811100399725079144771) * 10 ^ 70 +
        6497598316094194584005005672554555938147038278696568986450065171004154) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (269 - x)) = _
  rw [show 270 = 120 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (270 + x) *
        remainder6Coefficient1.coeff (270 - (270 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 270 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (270 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (270 - (270 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_270 :
    recurrence4Scalar1Exceptional.coeff 270 =
      (((((4070345730012094871011010720 * 10 ^ 70 +
        4203279648899498767806627153149930206594356535990254295792156149038534) * 10 ^ 70 +
        6575247618608696992969438618216772398921833908025331005829528374505526) * 10 ^ 70 +
        3441506429871307009444953430595654783958022236263054253943337498686499) * 10 ^ 70 +
        5753684845633863803129976609220220673988607709730810308406061786778979) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (270 - x)) = _
  rw [show 271 = 121 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (271 + x) *
        remainder6Coefficient1.coeff (271 - (271 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 271 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (271 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (271 - (271 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_271 :
    recurrence4Scalar1Exceptional.coeff 271 =
      -(((((3450734271080299749359766926 * 10 ^ 70 +
        0647063635581381096224037383083317628894125927644493152842582458242867) * 10 ^ 70 +
        5335835029105809567916261709065805577020813278130083250008803203942122) * 10 ^ 70 +
        0658370945974865090086860280058913108511644076343908256649191253273025) * 10 ^ 70 +
        2594977238535934444878152313563034426604177830526293026291722442975316) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (271 - x)) = _
  rw [show 272 = 122 +
    150 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 32 +
      54 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 54 = 32 +
      22 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 22 = 21 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
