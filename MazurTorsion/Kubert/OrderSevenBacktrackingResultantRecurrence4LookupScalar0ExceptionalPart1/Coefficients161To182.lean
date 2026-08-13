/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0ExceptionalPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4C0_coeff_1
  recurrence4C0_coeff_10
  recurrence4C0_coeff_100
  recurrence4C0_coeff_101
  recurrence4C0_coeff_102
  recurrence4C0_coeff_103
  recurrence4C0_coeff_104
  recurrence4C0_coeff_105
  recurrence4C0_coeff_106
  recurrence4C0_coeff_107
  recurrence4C0_coeff_108
  recurrence4C0_coeff_109
  recurrence4C0_coeff_11
  recurrence4C0_coeff_110
  recurrence4C0_coeff_111
  recurrence4C0_coeff_112
  recurrence4C0_coeff_113
  recurrence4C0_coeff_114
  recurrence4C0_coeff_115
  recurrence4C0_coeff_116
  recurrence4C0_coeff_117
  recurrence4C0_coeff_118
  recurrence4C0_coeff_119
  recurrence4C0_coeff_12
  recurrence4C0_coeff_120
  recurrence4C0_coeff_121
  recurrence4C0_coeff_122
  recurrence4C0_coeff_123
  recurrence4C0_coeff_124
  recurrence4C0_coeff_125
  recurrence4C0_coeff_126
  recurrence4C0_coeff_127
  recurrence4C0_coeff_128
  recurrence4C0_coeff_129
  recurrence4C0_coeff_13
  recurrence4C0_coeff_130
  recurrence4C0_coeff_131
  recurrence4C0_coeff_132
  recurrence4C0_coeff_133
  recurrence4C0_coeff_134
  recurrence4C0_coeff_135
  recurrence4C0_coeff_136
  recurrence4C0_coeff_137
  recurrence4C0_coeff_138
  recurrence4C0_coeff_139
  recurrence4C0_coeff_14
  recurrence4C0_coeff_140
  recurrence4C0_coeff_141
  recurrence4C0_coeff_142
  recurrence4C0_coeff_143
  recurrence4C0_coeff_144
  recurrence4C0_coeff_145
  recurrence4C0_coeff_146
  recurrence4C0_coeff_147
  recurrence4C0_coeff_148
  recurrence4C0_coeff_149
  recurrence4C0_coeff_15
  recurrence4C0_coeff_150
  recurrence4C0_coeff_151
  recurrence4C0_coeff_152
  recurrence4C0_coeff_153
  recurrence4C0_coeff_16
  recurrence4C0_coeff_17
  recurrence4C0_coeff_18

attribute [local simp]
  recurrence4C0_coeff_19
  recurrence4C0_coeff_2
  recurrence4C0_coeff_20
  recurrence4C0_coeff_21
  recurrence4C0_coeff_22
  recurrence4C0_coeff_23
  recurrence4C0_coeff_24
  recurrence4C0_coeff_25
  recurrence4C0_coeff_26
  recurrence4C0_coeff_27
  recurrence4C0_coeff_28
  recurrence4C0_coeff_29
  recurrence4C0_coeff_3
  recurrence4C0_coeff_30
  recurrence4C0_coeff_31
  recurrence4C0_coeff_32
  recurrence4C0_coeff_33
  recurrence4C0_coeff_34
  recurrence4C0_coeff_35
  recurrence4C0_coeff_36
  recurrence4C0_coeff_37
  recurrence4C0_coeff_38
  recurrence4C0_coeff_39
  recurrence4C0_coeff_4
  recurrence4C0_coeff_40
  recurrence4C0_coeff_41
  recurrence4C0_coeff_42
  recurrence4C0_coeff_43
  recurrence4C0_coeff_44
  recurrence4C0_coeff_45
  recurrence4C0_coeff_46
  recurrence4C0_coeff_47
  recurrence4C0_coeff_48
  recurrence4C0_coeff_49
  recurrence4C0_coeff_5
  recurrence4C0_coeff_50
  recurrence4C0_coeff_51
  recurrence4C0_coeff_52
  recurrence4C0_coeff_53
  recurrence4C0_coeff_54
  recurrence4C0_coeff_55
  recurrence4C0_coeff_56
  recurrence4C0_coeff_57
  recurrence4C0_coeff_58
  recurrence4C0_coeff_59
  recurrence4C0_coeff_6
  recurrence4C0_coeff_60
  recurrence4C0_coeff_61
  recurrence4C0_coeff_62
  recurrence4C0_coeff_63
  recurrence4C0_coeff_64
  recurrence4C0_coeff_65
  recurrence4C0_coeff_66
  recurrence4C0_coeff_67
  recurrence4C0_coeff_68
  recurrence4C0_coeff_69
  recurrence4C0_coeff_7
  recurrence4C0_coeff_70
  recurrence4C0_coeff_71
  recurrence4C0_coeff_72
  recurrence4C0_coeff_73
  recurrence4C0_coeff_74
  recurrence4C0_coeff_75
  recurrence4C0_coeff_76

attribute [local simp]
  recurrence4C0_coeff_77
  recurrence4C0_coeff_78
  recurrence4C0_coeff_79
  recurrence4C0_coeff_8
  recurrence4C0_coeff_80
  recurrence4C0_coeff_81
  recurrence4C0_coeff_82
  recurrence4C0_coeff_83
  recurrence4C0_coeff_84
  recurrence4C0_coeff_85
  recurrence4C0_coeff_86
  recurrence4C0_coeff_87
  recurrence4C0_coeff_88
  recurrence4C0_coeff_89
  recurrence4C0_coeff_9
  recurrence4C0_coeff_90
  recurrence4C0_coeff_91
  recurrence4C0_coeff_92
  recurrence4C0_coeff_93
  recurrence4C0_coeff_94
  recurrence4C0_coeff_95
  recurrence4C0_coeff_96
  recurrence4C0_coeff_97
  recurrence4C0_coeff_98
  recurrence4C0_coeff_99
  recurrence4ExceptionalProduct_coeff_10
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
  recurrence4ExceptionalProduct_coeff_11
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

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_135
  recurrence4ExceptionalProduct_coeff_136
  recurrence4ExceptionalProduct_coeff_137
  recurrence4ExceptionalProduct_coeff_138
  recurrence4ExceptionalProduct_coeff_139
  recurrence4ExceptionalProduct_coeff_14
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

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_193
  recurrence4ExceptionalProduct_coeff_194
  recurrence4ExceptionalProduct_coeff_195
  recurrence4ExceptionalProduct_coeff_196
  recurrence4ExceptionalProduct_coeff_197
  recurrence4ExceptionalProduct_coeff_198
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

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_251
  recurrence4ExceptionalProduct_coeff_252
  recurrence4ExceptionalProduct_coeff_253
  recurrence4ExceptionalProduct_coeff_254
  recurrence4ExceptionalProduct_coeff_255
  recurrence4ExceptionalProduct_coeff_256
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

attribute [local simp]
  recurrence4ExceptionalProduct_coeff_70
  recurrence4ExceptionalProduct_coeff_71
  recurrence4ExceptionalProduct_coeff_72
  recurrence4ExceptionalProduct_coeff_73
  recurrence4ExceptionalProduct_coeff_74
  recurrence4ExceptionalProduct_coeff_75
  recurrence4ExceptionalProduct_coeff_76
  recurrence4ExceptionalProduct_coeff_77
  recurrence4ExceptionalProduct_coeff_78
  recurrence4ExceptionalProduct_coeff_79
  recurrence4ExceptionalProduct_coeff_8
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
  recurrence4ExceptionalProduct_coeff_9
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

private theorem recurrence4Scalar0Exceptional_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (161 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (161 + x) *
        remainder6Coefficient0.coeff (161 - (161 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 161 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (161 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (161 - (161 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_161 :
    recurrence4Scalar0Exceptional.coeff 161 =
      -((((4576659579864059634418084040224647223288765356366562081240263696962670 * 10 ^ 70 +
        3319029951064647928931341367993406025879018810622801649793683121053069) * 10 ^ 70 +
        4514578839030622973805748462968482185185176347108875917244650106575856) * 10 ^ 70 +
        6678051748822202571643210457642678918336426120502615241305725535477991) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (161 - x)) = _
  rw [show 162 = 8 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_161_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_161_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (162 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (162 + x) *
        remainder6Coefficient0.coeff (162 - (162 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 162 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (162 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (162 - (162 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_162 :
    recurrence4Scalar0Exceptional.coeff 162 =
      (((((1 * 10 ^ 70 +
        9755119356675351595992077101960928664213486548533834413364746144280612) * 10 ^ 70 +
        4887765414485358541229969647437089969490413443499053805983164796020223) * 10 ^ 70 +
        3053728751114012944358526074275212544642338346777858968320594496210981) * 10 ^ 70 +
        5777332001673341606423184937042325130448546445327331293529783828758856) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (162 - x)) = _
  rw [show 163 = 9 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_162_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_162_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (163 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (163 + x) *
        remainder6Coefficient0.coeff (163 - (163 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 163 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (163 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (163 - (163 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_163 :
    recurrence4Scalar0Exceptional.coeff 163 =
      -(((((8 * 10 ^ 70 +
        3296143803615177598791296912620958871276833376801866478407777033499169) * 10 ^ 70 +
        9403763304977043847957565259799600572675050138225246094790861878608630) * 10 ^ 70 +
        4474506397299848889725249882653014541594033055299970802131599469692741) * 10 ^ 70 +
        6185778670499816710643184406705998870978396371097231056435645092534084) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (163 - x)) = _
  rw [show 164 = 10 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_163_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (164 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (164 + x) *
        remainder6Coefficient0.coeff (164 - (164 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 164 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (164 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (164 - (164 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_164 :
    recurrence4Scalar0Exceptional.coeff 164 =
      (((((34 * 10 ^ 70 +
        3381392349616735266487912978896749243550533659299786035576461135194353) * 10 ^ 70 +
        8771108537589435983079894850364737302787060684135867065359275145671329) * 10 ^ 70 +
        8513018685971361743474142120600077336299119537513565357854764291619767) * 10 ^ 70 +
        6431481385156843311549351153475802869977709933967884077614326533246132) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (164 - x)) = _
  rw [show 165 = 11 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_164_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (165 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (165 + x) *
        remainder6Coefficient0.coeff (165 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 165 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (165 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (165 - (165 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_165 :
    recurrence4Scalar0Exceptional.coeff 165 =
      -(((((138 * 10 ^ 70 +
        5058646094276538239706260518333599113505837965568122144558447749498004) * 10 ^ 70 +
        5983644873303424232260722470115853622279564771863662682688249048053299) * 10 ^ 70 +
        5970712992094096522670718980120981391417010090545464974158452151616932) * 10 ^ 70 +
        1623438408883423785378173394561925755080270590434287650973385541801040) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (165 - x)) = _
  rw [show 166 = 12 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (166 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (166 + x) *
        remainder6Coefficient0.coeff (166 - (166 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 166 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (166 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (166 - (166 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_166 :
    recurrence4Scalar0Exceptional.coeff 166 =
      (((((546 * 10 ^ 70 +
        9974518999449069271637046819180184170650798285311034896529466999361953) * 10 ^ 70 +
        2363030212003235625918658956605602564051751660700499662802548800372482) * 10 ^ 70 +
        8435962507939124096811519155546636619112644835406026739207584813088562) * 10 ^ 70 +
        4031132777879367302668290255441379649222830361999075407796901489612998) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (166 - x)) = _
  rw [show 167 = 13 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (167 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (167 + x) *
        remainder6Coefficient0.coeff (167 - (167 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 167 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (167 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (167 - (167 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_167 :
    recurrence4Scalar0Exceptional.coeff 167 =
      -(((((2116 * 10 ^ 70 +
        2991739499818013059455053959489235443556168891683396215940966467067618) * 10 ^ 70 +
        1146540084649549627073476547053422634624090260949488832706638030782597) * 10 ^ 70 +
        3008243509624374254537878011624069895655033811740882908528198108008845) * 10 ^ 70 +
        2964107736224412696919107245259679702582980221570562753507994518778848) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (167 - x)) = _
  rw [show 168 = 14 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (168 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (168 + x) *
        remainder6Coefficient0.coeff (168 - (168 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 168 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (168 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (168 - (168 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_168 :
    recurrence4Scalar0Exceptional.coeff 168 =
      (((((8025 * 10 ^ 70 +
        3152200359283994310475582545516871252196883060128566849953430444219980) * 10 ^ 70 +
        5889278666529816413934258390253280473088916481314758344267710369149858) * 10 ^ 70 +
        6937661182702881605036961328459672300330371198349909838479511275830872) * 10 ^ 70 +
        6244989673880295881515304069400688018032974062889920338654674536378713) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (168 - x)) = _
  rw [show 169 = 15 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (169 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (169 + x) *
        remainder6Coefficient0.coeff (169 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 169 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (169 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (169 - (169 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_169 :
    recurrence4Scalar0Exceptional.coeff 169 =
      -(((((29842 * 10 ^ 70 +
        4357719517338655238689776295925530228113293361646618102515479005197722) * 10 ^ 70 +
        4095454210211132369865158121702429134041181933148462169568050321670278) * 10 ^ 70 +
        6173587716060603918675277942249316872888261575272200945458688010665087) * 10 ^ 70 +
        2666394826529316206219031793946176741901060530882728167446307245402296) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (169 - x)) = _
  rw [show 170 = 16 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (170 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (170 + x) *
        remainder6Coefficient0.coeff (170 - (170 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 170 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (170 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (170 - (170 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_170 :
    recurrence4Scalar0Exceptional.coeff 170 =
      (((((108859 * 10 ^ 70 +
        6212695142372249188899909054741474978623929250227238238610110695149526) * 10 ^ 70 +
        6287985924721175354850939582042521882452280409427840167644360349895117) * 10 ^ 70 +
        5034743223711826167317773214061397046244773018785087173106988536725902) * 10 ^ 70 +
        8249257123070551321363588773239770724483122069116882091317354020692436) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (170 - x)) = _
  rw [show 171 = 17 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (171 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (171 + x) *
        remainder6Coefficient0.coeff (171 - (171 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 171 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (171 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (171 - (171 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_171 :
    recurrence4Scalar0Exceptional.coeff 171 =
      -(((((389686 * 10 ^ 70 +
        8194821209473604359302259926738104484434646146630629673909310675831097) * 10 ^ 70 +
        1069503207189379398436385239223541007445583270161850440097148640518313) * 10 ^ 70 +
        8177298140066803467056204004756064591340046231200088637682370825970701) * 10 ^ 70 +
        6609229559874986370435070025013262682334609542640459983871761473322838) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (171 - x)) = _
  rw [show 172 = 18 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (172 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (172 + x) *
        remainder6Coefficient0.coeff (172 - (172 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 172 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (172 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (172 - (172 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_172 :
    recurrence4Scalar0Exceptional.coeff 172 =
      (((((1369374 * 10 ^ 70 +
        6216061671634848639778772744928591509122609924792081309157718310474578) * 10 ^ 70 +
        4998839349762050334977013364844786240745027786252739529376915987336719) * 10 ^ 70 +
        3662965462353518815051379077752018052954686523145923670720886085500043) * 10 ^ 70 +
        2042073106789162379249532407853128290116297332264815153946682256326402) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (172 - x)) = _
  rw [show 173 = 19 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (173 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (173 + x) *
        remainder6Coefficient0.coeff (173 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 173 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (173 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (173 - (173 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_173 :
    recurrence4Scalar0Exceptional.coeff 173 =
      -(((((4725146 * 10 ^ 70 +
        5818009405092635425901055495958614706776613178366723966061041510992993) * 10 ^ 70 +
        5295235151710153327271880333645054640084871030196583658368911377302760) * 10 ^ 70 +
        1949845388031684974471069780313641286781046262169075552305802845850879) * 10 ^ 70 +
        9346722665001073191979125689232975638238871544268826058506060379768409) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (173 - x)) = _
  rw [show 174 = 20 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (174 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (174 + x) *
        remainder6Coefficient0.coeff (174 - (174 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 174 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (174 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (174 - (174 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_174 :
    recurrence4Scalar0Exceptional.coeff 174 =
      (((((16014476 * 10 ^ 70 +
        6842222093538707804672566171196477416421145818132687645560222671025539) * 10 ^ 70 +
        5631351913784854450977735535516932413356631578116759792066154173112401) * 10 ^ 70 +
        5403337099912929531804731572724305294202183583466818171697625580582714) * 10 ^ 70 +
        6364017005188328741112490800412944619727713150283273214646831535965136) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (174 - x)) = _
  rw [show 175 = 21 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (175 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (175 + x) *
        remainder6Coefficient0.coeff (175 - (175 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 175 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (175 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (175 - (175 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_175 :
    recurrence4Scalar0Exceptional.coeff 175 =
      -(((((53324072 * 10 ^ 70 +
        4834795049952122971515661558898675035040970839809690190944738527485652) * 10 ^ 70 +
        0593546922771836159838102459621528177472212724525215860250515644670068) * 10 ^ 70 +
        8175660252622144097223386079420405610041059557178456571533349059345979) * 10 ^ 70 +
        0811251354238224476071636757613434970075426032478718040213920136870048) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (175 - x)) = _
  rw [show 176 = 22 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (176 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (176 + x) *
        remainder6Coefficient0.coeff (176 - (176 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 176 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (176 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (176 - (176 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_176 :
    recurrence4Scalar0Exceptional.coeff 176 =
      (((((174480707 * 10 ^ 70 +
        7317671827678793705737529352957450115320910921740917029057579909683634) * 10 ^ 70 +
        2347291810656688632501655407493876991104486420174230949375378470977659) * 10 ^ 70 +
        0293277016236665097208793113518162423391844747835245203458319408471247) * 10 ^ 70 +
        5147714078566956467718293653670479440215911950228560755793893043643551) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (176 - x)) = _
  rw [show 177 = 23 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (177 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (177 + x) *
        remainder6Coefficient0.coeff (177 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 177 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (177 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (177 - (177 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_177 :
    recurrence4Scalar0Exceptional.coeff 177 =
      -(((((561149161 * 10 ^ 70 +
        7951092211082337257804729598160360547295823658007768733943025956129220) * 10 ^ 70 +
        4376022427787733806011178641674092849815553100178530830895700704581272) * 10 ^ 70 +
        0680816272703938932065004068810538528878474883633604893018048202215959) * 10 ^ 70 +
        4945687440407178805209940683923110607352547898647887845025386825488219) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (177 - x)) = _
  rw [show 178 = 24 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (178 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (178 + x) *
        remainder6Coefficient0.coeff (178 - (178 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 178 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (178 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (178 - (178 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_178 :
    recurrence4Scalar0Exceptional.coeff 178 =
      (((((1774201370 * 10 ^ 70 +
        7341897238979039281292931414166125165448462976355035564388291193147595) * 10 ^ 70 +
        0865650124398567078325795156965332233437285528043892814390227672835147) * 10 ^ 70 +
        7851473207241904994889776372314011403092840458558136907697302212251017) * 10 ^ 70 +
        7990466929452316936102116443407084390593059793211330145885524511794979) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (178 - x)) = _
  rw [show 179 = 25 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (179 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (179 + x) *
        remainder6Coefficient0.coeff (179 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 179 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (179 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (179 - (179 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_179 :
    recurrence4Scalar0Exceptional.coeff 179 =
      -(((((5515722563 * 10 ^ 70 +
        4428300949643702497652998671498699720090925322742424642385106386072619) * 10 ^ 70 +
        9281838796433007312602730927020855213667382586784654288885582579871114) * 10 ^ 70 +
        4217995614353783811392995022028078751573981499712151834232836040056341) * 10 ^ 70 +
        3480079802893136601293542654723579509381448917970485156452750922023157) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (179 - x)) = _
  rw [show 180 = 26 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (180 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (180 + x) *
        remainder6Coefficient0.coeff (180 - (180 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 180 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (180 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (180 - (180 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_180 :
    recurrence4Scalar0Exceptional.coeff 180 =
      (((((16863704646 * 10 ^ 70 +
        0152662629902056493959834936121085539027249452866808079480710089185850) * 10 ^ 70 +
        8849370534934151502958257584156709717202859786398519196447190652140104) * 10 ^ 70 +
        3298613989785045340474459843861276265453914786403995252963668433127571) * 10 ^ 70 +
        6756520938534818156860808712197149714336927165934732237035551134797950) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (180 - x)) = _
  rw [show 181 = 27 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (181 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (181 + x) *
        remainder6Coefficient0.coeff (181 - (181 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 181 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (181 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (181 - (181 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_181 :
    recurrence4Scalar0Exceptional.coeff 181 =
      -(((((50713810492 * 10 ^ 70 +
        4772340863300618643697964346989107166751493262854161751055467546701298) * 10 ^ 70 +
        6356108580964001631897587677523707431703299112254104858914348435311708) * 10 ^ 70 +
        8174925001327616774301729104383832375700883104034556601009911084295899) * 10 ^ 70 +
        9529559822765237302985661786767209776550966985509654539522151642574187) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (181 - x)) = _
  rw [show 182 = 28 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Exceptional_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (182 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (182 + x) *
        remainder6Coefficient0.coeff (182 - (182 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 182 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (182 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (182 - (182 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_182 :
    recurrence4Scalar0Exceptional.coeff 182 =
      (((((150034000181 * 10 ^ 70 +
        9884811421028551263973875754637249159071162106408397827218520813186030) * 10 ^ 70 +
        6735309442633134183634418011313704879310631106855138176064413140291101) * 10 ^ 70 +
        2461103794406614422741283913938825039197506566656248429968791686804346) * 10 ^ 70 +
        1990862637358141996389273221175981266278111788595513149271786237174133) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (182 - x)) = _
  rw [show 183 = 29 +
    154 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 32 +
      58 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 58 = 32 +
      26 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 26 = 25 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Exceptional_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
