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

private theorem recurrence4Scalar1Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (205 + x) *
        remainder6Coefficient1.coeff (205 - (205 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 205 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (205 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (205 - (205 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_205 :
    recurrence4Scalar1Exceptional.coeff 205 =
      -(((((96324750254617888378 * 10 ^ 70 +
        1398623071739271581742596690625803252924011889464512957483905986166797) * 10 ^ 70 +
        3210891456806621694124543358438658300924853396940608417676726117244020) * 10 ^ 70 +
        5471556109831502042406026474438563702795359445712710100811204058773632) * 10 ^ 70 +
        0037888253263080824799061595775109381866566821347059401139272059478514) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (205 - x)) = _
  rw [show 206 = 56 +
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
  rw [recurrence4Scalar1Exceptional_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_205_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (206 + x) *
        remainder6Coefficient1.coeff (206 - (206 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 206 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (206 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (206 - (206 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_206 :
    recurrence4Scalar1Exceptional.coeff 206 =
      (((((194491404210799357801 * 10 ^ 70 +
        1824225426491771030744984949996002838647985784702023507112484021412938) * 10 ^ 70 +
        0030449716456642657501313944533139086320735245782628831014584758359226) * 10 ^ 70 +
        1258381873528626706149292095970998252855307601387295540010468060374238) * 10 ^ 70 +
        0351178997996333848496874199781924963957919165551956292231930974942172) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (206 - x)) = _
  rw [show 207 = 57 +
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
  rw [recurrence4Scalar1Exceptional_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_206_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (207 + x) *
        remainder6Coefficient1.coeff (207 - (207 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 207 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (207 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (207 - (207 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_207 :
    recurrence4Scalar1Exceptional.coeff 207 =
      -(((((387168414651344971576 * 10 ^ 70 +
        9964078610019737547956581355036540448559933601251110797014284264412613) * 10 ^ 70 +
        0654867312580059604152582127231545130323359271118084640517168495367927) * 10 ^ 70 +
        3392503992040551706778276655056597943937081777713300078066322017591723) * 10 ^ 70 +
        1195658242635801966817393280464803198593442784340755423060135510757883) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (207 - x)) = _
  rw [show 208 = 58 +
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
  rw [recurrence4Scalar1Exceptional_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_207_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (208 + x) *
        remainder6Coefficient1.coeff (208 - (208 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 208 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (208 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (208 - (208 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_208 :
    recurrence4Scalar1Exceptional.coeff 208 =
      (((((759904313915260319701 * 10 ^ 70 +
        5678928573076803688718554041098394995716636631235726531482404994293483) * 10 ^ 70 +
        8719939490129543680086220010387619825240006891642424396085475192424800) * 10 ^ 70 +
        0911687720496325481143456236622514983314553512798849385303890007090813) * 10 ^ 70 +
        5100855609246072677138067471727361503162686537185930912976330379997211) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (208 - x)) = _
  rw [show 209 = 59 +
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
  rw [recurrence4Scalar1Exceptional_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_208_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (209 + x) *
        remainder6Coefficient1.coeff (209 - (209 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 209 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (209 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (209 - (209 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_209 :
    recurrence4Scalar1Exceptional.coeff 209 =
      -(((((1470615497181496186087 * 10 ^ 70 +
        3724373144448858785897331069043505868846186053457545720510545791018147) * 10 ^ 70 +
        8724129565229792345454879789039837944169601013851785105027743953313279) * 10 ^ 70 +
        8124797898976951405289168601292107216419282232781191319693808889494665) * 10 ^ 70 +
        5833825951404422752743695221478716978178234917330785158274994581554719) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (209 - x)) = _
  rw [show 210 = 60 +
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
  rw [recurrence4Scalar1Exceptional_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_209_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (210 + x) *
        remainder6Coefficient1.coeff (210 - (210 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 210 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (210 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (210 - (210 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_210 :
    recurrence4Scalar1Exceptional.coeff 210 =
      (((((2806348816550092411556 * 10 ^ 70 +
        8640322757547995538409518603639799564356403090621098781331390134100406) * 10 ^ 70 +
        0888451133293732626763613645938399750417179215616514647907903140135732) * 10 ^ 70 +
        3313132208874504531551772262380297452972693045088112785276004500964054) * 10 ^ 70 +
        0786375079732146943914491659147300024194057134042910884739626300086422) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (210 - x)) = _
  rw [show 211 = 61 +
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
  rw [recurrence4Scalar1Exceptional_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_210_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (211 + x) *
        remainder6Coefficient1.coeff (211 - (211 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 211 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (211 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (211 - (211 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_211 :
    recurrence4Scalar1Exceptional.coeff 211 =
      -(((((5280886180889498999118 * 10 ^ 70 +
        2067413528483802303654345540228180087135087548244011836928963537596149) * 10 ^ 70 +
        8476641430920708066249122694568913270072350892976522665283325297989954) * 10 ^ 70 +
        0834650106137404233968273837688348147213768220080216879733268623887221) * 10 ^ 70 +
        4392832553758677673938238550969467610392170729204156415324009146570988) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (211 - x)) = _
  rw [show 212 = 62 +
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
  rw [recurrence4Scalar1Exceptional_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_211_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (212 + x) *
        remainder6Coefficient1.coeff (212 - (212 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 212 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (212 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (212 - (212 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_212 :
    recurrence4Scalar1Exceptional.coeff 212 =
      (((((9799734325393452126808 * 10 ^ 70 +
        9559165389209132968574577587556126268132623113996863822433191882905975) * 10 ^ 70 +
        0921212604376194914636470821362470991112872356498789112903430948814006) * 10 ^ 70 +
        5646854673994312610416465526317018966754372911002326922621312049181709) * 10 ^ 70 +
        5774414279441461739591167210306409726008503974607241312471874076262634) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (212 - x)) = _
  rw [show 213 = 63 +
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
  rw [recurrence4Scalar1Exceptional_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_212_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (213 + x) *
        remainder6Coefficient1.coeff (213 - (213 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 213 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (213 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (213 - (213 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_213 :
    recurrence4Scalar1Exceptional.coeff 213 =
      -(((((17934248639367832298278 * 10 ^ 70 +
        9737288329613467125267252828634820253228443284422279899516621981520153) * 10 ^ 70 +
        8059861382916615685422075797213825947685383084858006496385078484450681) * 10 ^ 70 +
        7856536149913019948944504800145570551661064558493175090488245410840614) * 10 ^ 70 +
        0816774845832859783388139320394390163800822134479544371390867459937143) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (213 - x)) = _
  rw [show 214 = 64 +
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
  rw [recurrence4Scalar1Exceptional_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_213_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (214 + x) *
        remainder6Coefficient1.coeff (214 - (214 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 214 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (214 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (214 - (214 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_214 :
    recurrence4Scalar1Exceptional.coeff 214 =
      (((((32369194226759684340563 * 10 ^ 70 +
        8490316101151874613017660584089797145032747958410789241056703412262722) * 10 ^ 70 +
        0076014355855964643942328435571447498130710958748487032934631579231032) * 10 ^ 70 +
        5489661056585800091298701144951235341033773693598015824363847349134417) * 10 ^ 70 +
        6528310107702412433043780826831328131183741716809116679793824143788737) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (214 - x)) = _
  rw [show 215 = 65 +
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
  rw [recurrence4Scalar1Exceptional_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_214_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (215 + x) *
        remainder6Coefficient1.coeff (215 - (215 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 215 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (215 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (215 - (215 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_215 :
    recurrence4Scalar1Exceptional.coeff 215 =
      -(((((57620660284139169200772 * 10 ^ 70 +
        7125730493552030751366194659878324436126929001060011829962724016384399) * 10 ^ 70 +
        4263127449883106747887496818557611503703162400954705922089947965780497) * 10 ^ 70 +
        5910874300690728151562688647678231941319825098662291667381533877253556) * 10 ^ 70 +
        5102349858436420673470189449911780948081100062325982577596040815578547) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (215 - x)) = _
  rw [show 216 = 66 +
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
  rw [recurrence4Scalar1Exceptional_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_215_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (216 + x) *
        remainder6Coefficient1.coeff (216 - (216 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 216 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (216 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (216 - (216 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_216 :
    recurrence4Scalar1Exceptional.coeff 216 =
      (((((101167134103616419335421 * 10 ^ 70 +
        2524059696239456485136256980289439706253004733120007682850916849777903) * 10 ^ 70 +
        7926387751137541814790785051083956977395858491871131520432310860221478) * 10 ^ 70 +
        6728330211306531925126823909712178737065748875272253761493578494107764) * 10 ^ 70 +
        5241901184784060113686528505381052475472552981975421547255882877844880) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (216 - x)) = _
  rw [show 217 = 67 +
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
  rw [recurrence4Scalar1Exceptional_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_216_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (217 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (217 + x) *
        remainder6Coefficient1.coeff (217 - (217 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 217 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (217 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (217 - (217 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_217 :
    recurrence4Scalar1Exceptional.coeff 217 =
      -(((((175199233471222422856627 * 10 ^ 70 +
        7014241772610281957855933914454931648734666699426051982068788602801122) * 10 ^ 70 +
        4155820289379318718701474120814626089610839026939204031820034768574964) * 10 ^ 70 +
        5043857986292364264429711734122909122086967386480626161635619753432537) * 10 ^ 70 +
        8375197832517323630779416901602195190383914867067067392660808530368992) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (217 - x)) = _
  rw [show 218 = 68 +
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
  rw [recurrence4Scalar1Exceptional_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_217_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (218 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (218 + x) *
        remainder6Coefficient1.coeff (218 - (218 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 218 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (218 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (218 - (218 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_218 :
    recurrence4Scalar1Exceptional.coeff 218 =
      (((((299276489226790133963937 * 10 ^ 70 +
        3462024965798872762292631214164445904963238784882066053618081966083993) * 10 ^ 70 +
        5976353090561391084282124407547598349649834740019531872967038457502026) * 10 ^ 70 +
        1992197487818191659504397181454660057928974743981584100634508295510503) * 10 ^ 70 +
        2192622298267228754129868122643908092883089023501057453931914829206603) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (218 - x)) = _
  rw [show 219 = 69 +
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
  rw [recurrence4Scalar1Exceptional_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_218_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (219 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (219 + x) *
        remainder6Coefficient1.coeff (219 - (219 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 219 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (219 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (219 - (219 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_219 :
    recurrence4Scalar1Exceptional.coeff 219 =
      -(((((504285184143773126023247 * 10 ^ 70 +
        0061903825369897690450925923790026560876993744128798534559211955909122) * 10 ^ 70 +
        4867908995099174051667743878082870901828340415925136863098637717539103) * 10 ^ 70 +
        6898591735636992181429177945990912051432708832838490549491101488174960) * 10 ^ 70 +
        5455235982427463644943714333141399850827170214401571327219110453106886) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (219 - x)) = _
  rw [show 220 = 70 +
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
  rw [recurrence4Scalar1Exceptional_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_219_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (220 + x) *
        remainder6Coefficient1.coeff (220 - (220 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 220 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (220 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (220 - (220 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_220 :
    recurrence4Scalar1Exceptional.coeff 220 =
      (((((838220085263149028473527 * 10 ^ 70 +
        2202833312653911100022583025206816184801717765333337206496084530418920) * 10 ^ 70 +
        4734454833338924849360987475406058365752600503325778214491272323354403) * 10 ^ 70 +
        9805890667867994308568353562128296512492213565295431429166457258766846) * 10 ^ 70 +
        6878559806065884553916541151740267069243104559976418688573484007137032) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (220 - x)) = _
  rw [show 221 = 71 +
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
  rw [recurrence4Scalar1Exceptional_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_220_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (221 + x) *
        remainder6Coefficient1.coeff (221 - (221 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 221 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (221 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (221 - (221 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_221 :
    recurrence4Scalar1Exceptional.coeff 221 =
      -(((((1374461833114874632099671 * 10 ^ 70 +
        2580170820153760555308569969430390073585714659300239009022954076688831) * 10 ^ 70 +
        4087346578022442703693978993929339954650386059280340484806423799256731) * 10 ^ 70 +
        7513690768801700001994460445880832572351815883227772258505489008084626) * 10 ^ 70 +
        2457410995881205786582890649997523466205487254353123095311930245511544) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (221 - x)) = _
  rw [show 222 = 72 +
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
  rw [recurrence4Scalar1Exceptional_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_221_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (222 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (222 + x) *
        remainder6Coefficient1.coeff (222 - (222 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 222 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (222 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (222 - (222 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_222 :
    recurrence4Scalar1Exceptional.coeff 222 =
      (((((2223382028761583887693998 * 10 ^ 70 +
        3448891320840507047230257974981616939029173825989676489105419795171266) * 10 ^ 70 +
        1979129469870399279205537105287185617733726519117758219119380842495603) * 10 ^ 70 +
        5053863449174701754108340219722084922350734295040117689916063597677242) * 10 ^ 70 +
        2273368673130746694251712682395167675514975742765831787937020642952416) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (222 - x)) = _
  rw [show 223 = 73 +
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
  rw [recurrence4Scalar1Exceptional_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_222_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (223 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (223 + x) *
        remainder6Coefficient1.coeff (223 - (223 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 223 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (223 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (223 - (223 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_223 :
    recurrence4Scalar1Exceptional.coeff 223 =
      -(((((3548263043717062662890375 * 10 ^ 70 +
        8319492357045707089640898956708586423970693995574410209282642123007272) * 10 ^ 70 +
        1400250263047121296317838982150096803303666328982336828695021048703192) * 10 ^ 70 +
        4262746227149355227143097512205375518462447184527856087938722027476820) * 10 ^ 70 +
        3087671800027156677863624177248794453955139449726610133852951463243548) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (223 - x)) = _
  rw [show 224 = 74 +
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
  rw [recurrence4Scalar1Exceptional_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_223_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (224 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (224 + x) *
        remainder6Coefficient1.coeff (224 - (224 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 224 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (224 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (224 - (224 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_224 :
    recurrence4Scalar1Exceptional.coeff 224 =
      (((((5586642483559472716473929 * 10 ^ 70 +
        8935324613463845396479635634000256294405941448879596422174206375376814) * 10 ^ 70 +
        4997224377212303240264034250921230318968927774109761052436033490519216) * 10 ^ 70 +
        4076237641367664208127460493991176439816882117219873705933569387034825) * 10 ^ 70 +
        1074506073141509786972589890447521157420412427092337140246276480155163) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (224 - x)) = _
  rw [show 225 = 75 +
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
  rw [recurrence4Scalar1Exceptional_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_224_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (225 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (225 + x) *
        remainder6Coefficient1.coeff (225 - (225 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 225 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (225 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (225 - (225 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_225 :
    recurrence4Scalar1Exceptional.coeff 225 =
      -(((((8678244444709577090063424 * 10 ^ 70 +
        4801116710040842533957541132427907280985726460128605774200158620043683) * 10 ^ 70 +
        9811255778538856061889058080912967567618992217656071656203736802130672) * 10 ^ 70 +
        5470302767224621992099153111212976772445939493142347324405109836057906) * 10 ^ 70 +
        4982381818980317899294216452457805843047965847279781081040052991625798) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (225 - x)) = _
  rw [show 226 = 76 +
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
  rw [recurrence4Scalar1Exceptional_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Exceptional_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (226 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (226 + x) *
        remainder6Coefficient1.coeff (226 - (226 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 226 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (226 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (226 - (226 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_226 :
    recurrence4Scalar1Exceptional.coeff 226 =
      (((((13300590331285146684722131 * 10 ^ 70 +
        4507569952261269512356436089797636752505356220649039871977457812092776) * 10 ^ 70 +
        9627285123888756248234494325544097784822728740179904514726130301224820) * 10 ^ 70 +
        1828660603036536345778599333139787301598155097878694707842872109559170) * 10 ^ 70 +
        7492300440143480564794233675754238957466305764724799234515857254938214) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (226 - x)) = _
  rw [show 227 = 77 +
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
  rw [recurrence4Scalar1Exceptional_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
