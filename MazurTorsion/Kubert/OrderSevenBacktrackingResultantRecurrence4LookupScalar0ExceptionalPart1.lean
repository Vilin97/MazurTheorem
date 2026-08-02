/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (183 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (183 + x) *
        remainder6Coefficient0.coeff (183 - (183 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 183 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (183 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (183 - (183 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_183 :
    recurrence4Scalar0Exceptional.coeff 183 =
      -(((((436724050860 * 10 ^ 70 +
        2238078987226894300742285428380513036339253423768740305070122906288403) * 10 ^ 70 +
        5760436645167046773854315510636298396574111254668728967762303518425118) * 10 ^ 70 +
        7964701249574865688921900428029988521937631728674195181703613423291270) * 10 ^ 70 +
        6127124688549098370800990433917087324063721464187889908650411435446365) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (183 - x)) = _
  rw [show 184 = 30 +
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
  rw [recurrence4Scalar0Exceptional_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (184 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (184 + x) *
        remainder6Coefficient0.coeff (184 - (184 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 184 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (184 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (184 - (184 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_184 :
    recurrence4Scalar0Exceptional.coeff 184 =
      (((((1250946999617 * 10 ^ 70 +
        6396278916368107402372618397390795402381310488846816229365374358743509) * 10 ^ 70 +
        3253906218134134379624459762929375593079426996648220263206936267979846) * 10 ^ 70 +
        3325554795548178565940105372288724790815522574935137109104098262445583) * 10 ^ 70 +
        5459857279413985822225370702769628687827801739325041436379652717387803) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (184 - x)) = _
  rw [show 185 = 31 +
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
  rw [recurrence4Scalar0Exceptional_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (185 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (185 + x) *
        remainder6Coefficient0.coeff (185 - (185 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 185 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (185 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (185 - (185 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_185 :
    recurrence4Scalar0Exceptional.coeff 185 =
      -(((((3526487926807 * 10 ^ 70 +
        0281808194795276991938582625281274868273308209378158100700168048471978) * 10 ^ 70 +
        4205444099632859972890281512555915984359909227863849721873090829506681) * 10 ^ 70 +
        5075511331502019659604449231865413891606277239473032039647632589951449) * 10 ^ 70 +
        8493813231669579954245337622223741044892499041696367362936856336622612) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (185 - x)) = _
  rw [show 186 = 32 +
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
  rw [recurrence4Scalar0Exceptional_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (186 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (186 + x) *
        remainder6Coefficient0.coeff (186 - (186 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 186 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (186 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (186 - (186 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_186 :
    recurrence4Scalar0Exceptional.coeff 186 =
      (((((9785253112727 * 10 ^ 70 +
        9944033488455863680364724627186358209748197614077950661319102314438573) * 10 ^ 70 +
        0958558570075311253645249761280403216357356646108370709322655680182878) * 10 ^ 70 +
        6857865519800894885574036396972601003817881768659658752007976497357074) * 10 ^ 70 +
        0395244534204613940437341687941438165637353845961450924111124364170916) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (186 - x)) = _
  rw [show 187 = 33 +
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
  rw [recurrence4Scalar0Exceptional_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (187 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (187 + x) *
        remainder6Coefficient0.coeff (187 - (187 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 187 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (187 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (187 - (187 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_187 :
    recurrence4Scalar0Exceptional.coeff 187 =
      -(((((26728819127877 * 10 ^ 70 +
        2045409531823376123982015061322457540819574800205176355421191848840170) * 10 ^ 70 +
        7126064152944526666034099414750991608574386703115622781872250732697032) * 10 ^ 70 +
        4639031233465703823213132957056827547900546356193290973273412851459323) * 10 ^ 70 +
        6384153367780922555288994621739886155591317409414649157913417933199708) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (187 - x)) = _
  rw [show 188 = 34 +
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
  rw [recurrence4Scalar0Exceptional_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (188 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (188 + x) *
        remainder6Coefficient0.coeff (188 - (188 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 188 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (188 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (188 - (188 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_188 :
    recurrence4Scalar0Exceptional.coeff 188 =
      (((((71881146791408 * 10 ^ 70 +
        3610872547178416063325737423865498623332685322947360244526120332768837) * 10 ^ 70 +
        7739904246249890788503654502696305267344599143138009031745454401316515) * 10 ^ 70 +
        3726659669089754018502670099157084731114925763924321430360816107274200) * 10 ^ 70 +
        1885704439477840066005825703785737176666698078002708283777008667106112) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (188 - x)) = _
  rw [show 189 = 35 +
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
  rw [recurrence4Scalar0Exceptional_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (189 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (189 + x) *
        remainder6Coefficient0.coeff (189 - (189 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 189 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (189 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (189 - (189 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_189 :
    recurrence4Scalar0Exceptional.coeff 189 =
      -(((((190337774051574 * 10 ^ 70 +
        8078082315250396065114386907770103381705249984501099612493870974181064) * 10 ^ 70 +
        9614784425224379840279518355263877314543527770593247071878866389280577) * 10 ^ 70 +
        1758540618382712903356155307312306833683385664083814783274620874424557) * 10 ^ 70 +
        0355130424282967805769236237232729484681617056809826249361665057398936) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (189 - x)) = _
  rw [show 190 = 36 +
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
  rw [recurrence4Scalar0Exceptional_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (190 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (190 + x) *
        remainder6Coefficient0.coeff (190 - (190 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 190 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (190 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (190 - (190 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_190 :
    recurrence4Scalar0Exceptional.coeff 190 =
      (((((496312166158696 * 10 ^ 70 +
        8273818171501425159959617822939372242546783486933447458954708923912227) * 10 ^ 70 +
        8062370505194007486446999596705754594355617867419263813497947033111724) * 10 ^ 70 +
        8917569488840586917920353414587750617870679591674642593058473003441558) * 10 ^ 70 +
        8555400693379363316772376651686189669142425854504003126559969909509892) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (190 - x)) = _
  rw [show 191 = 37 +
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
  rw [recurrence4Scalar0Exceptional_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (191 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (191 + x) *
        remainder6Coefficient0.coeff (191 - (191 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 191 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (191 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (191 - (191 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_191 :
    recurrence4Scalar0Exceptional.coeff 191 =
      -(((((1274524135640098 * 10 ^ 70 +
        5359871082407591485386606725003408037558975933217574582045060309273013) * 10 ^ 70 +
        8015129154359406376785006879595957328579467766794266456422390310153472) * 10 ^ 70 +
        8728376256819778729253472028724371151110638672429518833799957768528645) * 10 ^ 70 +
        6002013128168499112191886460292360133428732110707538100993368516957701) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (191 - x)) = _
  rw [show 192 = 38 +
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
  rw [recurrence4Scalar0Exceptional_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (192 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (192 + x) *
        remainder6Coefficient0.coeff (192 - (192 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 192 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (192 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (192 - (192 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_192 :
    recurrence4Scalar0Exceptional.coeff 192 =
      (((((3223635153838406 * 10 ^ 70 +
        2451348557281925029489220743577589834068383450900219100575190249117758) * 10 ^ 70 +
        0975624717030103908726424663355050741996954269575723765207362652481722) * 10 ^ 70 +
        6635646108499547176352353720252315178817452258225052544177096392060683) * 10 ^ 70 +
        2945616704783953213460991647687244111300833601550626113712721967503947) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (192 - x)) = _
  rw [show 193 = 39 +
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
  rw [recurrence4Scalar0Exceptional_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (193 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (193 + x) *
        remainder6Coefficient0.coeff (193 - (193 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 193 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (193 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (193 - (193 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_193 :
    recurrence4Scalar0Exceptional.coeff 193 =
      -(((((8031342916641820 * 10 ^ 70 +
        4489553315218960730566439190454461609802212247346051399788510503802197) * 10 ^ 70 +
        0503280588208219003935455447170305667180902948602796609380698386563893) * 10 ^ 70 +
        7655494799005378584105607007800557246302019289166996425979555762660471) * 10 ^ 70 +
        2582633593234267845249156402545381088829822898678214234677123011382727) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (193 - x)) = _
  rw [show 194 = 40 +
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
  rw [recurrence4Scalar0Exceptional_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (194 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (194 + x) *
        remainder6Coefficient0.coeff (194 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 194 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (194 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (194 - (194 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_194 :
    recurrence4Scalar0Exceptional.coeff 194 =
      (((((19711203500037399 * 10 ^ 70 +
        9676782211543315811006573869835576938363382511465429059535561004434346) * 10 ^ 70 +
        6521698315927630101655829269780578625466009999458523928124712110774031) * 10 ^ 70 +
        4434823754000242120094516853651207479284298059675465642597081570182075) * 10 ^ 70 +
        7000824121429695321414034969604031317493878519686596509934153463636926) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (194 - x)) = _
  rw [show 195 = 41 +
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
  rw [recurrence4Scalar0Exceptional_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (195 + x) *
        remainder6Coefficient0.coeff (195 - (195 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 195 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (195 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (195 - (195 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_195 :
    recurrence4Scalar0Exceptional.coeff 195 =
      -(((((47660384274342826 * 10 ^ 70 +
        2881548292052683213222529479565534959327247253158287964738035065947857) * 10 ^ 70 +
        8944034971593558581433956282631397376716957967464280891305513856765344) * 10 ^ 70 +
        3738337062032187531859601868354922842462763656333498205956453643425112) * 10 ^ 70 +
        1388361498766650223019363377601463355274390320589085302842854549798221) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (195 - x)) = _
  rw [show 196 = 42 +
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
  rw [recurrence4Scalar0Exceptional_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (196 + x) *
        remainder6Coefficient0.coeff (196 - (196 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 196 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (196 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (196 - (196 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_196 :
    recurrence4Scalar0Exceptional.coeff 196 =
      (((((113542044721923034 * 10 ^ 70 +
        1989727177114716393457141496330763276827409309242678863203822732922886) * 10 ^ 70 +
        5988531373158591446969686738700602102076706914834573821268428357628352) * 10 ^ 70 +
        1490341987325279924235323202409109551552827715770839830113207734150254) * 10 ^ 70 +
        7743908083318945241591989206000698185835895202315431617730316377144091) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (196 - x)) = _
  rw [show 197 = 43 +
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
  rw [recurrence4Scalar0Exceptional_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (197 + x) *
        remainder6Coefficient0.coeff (197 - (197 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 197 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (197 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (197 - (197 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_197 :
    recurrence4Scalar0Exceptional.coeff 197 =
      -(((((266529134227148203 * 10 ^ 70 +
        9291713658179911428705098270165183304380316220291437814160477144719798) * 10 ^ 70 +
        5943471487906092209022966073088072072927152812925870122267837404098025) * 10 ^ 70 +
        4672343345096710173488623438008890297292890846832622889781914478155407) * 10 ^ 70 +
        7665340802188688964552975178524577303561425532699847692373298460530677) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (197 - x)) = _
  rw [show 198 = 44 +
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
  rw [recurrence4Scalar0Exceptional_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (198 + x) *
        remainder6Coefficient0.coeff (198 - (198 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 198 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (198 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (198 - (198 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_198 :
    recurrence4Scalar0Exceptional.coeff 198 =
      (((((616530068317523938 * 10 ^ 70 +
        4844918642585353254903817809729377538220199532878826147771040360472690) * 10 ^ 70 +
        7231094045077857761003813440900259141629231271618652558419096511185961) * 10 ^ 70 +
        3765577427874069231168106194305343026573433261543063912138911053049803) * 10 ^ 70 +
        3173125950062764033443742596719971092493402031039304831692113633974721) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (198 - x)) = _
  rw [show 199 = 45 +
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
  rw [recurrence4Scalar0Exceptional_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (199 + x) *
        remainder6Coefficient0.coeff (199 - (199 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 199 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (199 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (199 - (199 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_199 :
    recurrence4Scalar0Exceptional.coeff 199 =
      -(((((1405455316889772225 * 10 ^ 70 +
        9420389135272860819776863081289851027726367439876828440411387656824915) * 10 ^ 70 +
        2977892483531471971662058714030484798649231491524738099793916784789722) * 10 ^ 70 +
        5339186893411872896215021478072080645281283119594623888680728905145407) * 10 ^ 70 +
        5798888330288574258173580435983564406371029926915000618296916873259337) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (199 - x)) = _
  rw [show 200 = 46 +
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
  rw [recurrence4Scalar0Exceptional_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (200 + x) *
        remainder6Coefficient0.coeff (200 - (200 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 200 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (200 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (200 - (200 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_200 :
    recurrence4Scalar0Exceptional.coeff 200 =
      (((((3157646603970892385 * 10 ^ 70 +
        0071161287967915936300216302093253565887037294352118414805512016618928) * 10 ^ 70 +
        7820121386691931997807041004572495005744883697081265528950534472609173) * 10 ^ 70 +
        2827008755801225014552876170360141700999665765471212257862958339251246) * 10 ^ 70 +
        9855318272708090927385058781536382943828070846134276610772050435574055) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (200 - x)) = _
  rw [show 201 = 47 +
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
  rw [recurrence4Scalar0Exceptional_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (201 + x) *
        remainder6Coefficient0.coeff (201 - (201 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 201 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (201 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (201 - (201 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_201 :
    recurrence4Scalar0Exceptional.coeff 201 =
      -(((((6992349567807771594 * 10 ^ 70 +
        5088130672378665963962866852856259293622506493535831984755085530918168) * 10 ^ 70 +
        8907716019487798888123571841756406583830032704261494954844181763670244) * 10 ^ 70 +
        2589198004580747117095113835822603649019085807907919169068684363637529) * 10 ^ 70 +
        0729589216119439191985381414680221092162629223392760128387800129512451) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (201 - x)) = _
  rw [show 202 = 48 +
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
  rw [recurrence4Scalar0Exceptional_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (202 + x) *
        remainder6Coefficient0.coeff (202 - (202 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 202 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (202 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (202 - (202 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_202 :
    recurrence4Scalar0Exceptional.coeff 202 =
      (((((15262451019796098628 * 10 ^ 70 +
        6035671275624434908306506882477310883616321707014137445817578532781771) * 10 ^ 70 +
        7358964967867672888203253274903154187041857809845674187012179254307933) * 10 ^ 70 +
        5309395811440387909344679552090607337728094231810145536745354701341886) * 10 ^ 70 +
        0213575643695808161696920117703471209815232062775805949890961794705983) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (202 - x)) = _
  rw [show 203 = 49 +
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
  rw [recurrence4Scalar0Exceptional_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (203 + x) *
        remainder6Coefficient0.coeff (203 - (203 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 203 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (203 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (203 - (203 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_203 :
    recurrence4Scalar0Exceptional.coeff 203 =
      -(((((32839340340781818101 * 10 ^ 70 +
        7339765890504288759404959394488724768931282292116079408909473771537241) * 10 ^ 70 +
        2930839162503684713060372925630064717187870783215618608137639704203980) * 10 ^ 70 +
        9376101101578122207148162761081598658426224723555172922313057291970482) * 10 ^ 70 +
        1251807504302117876645067334259157439651991859836501537184142299905546) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (203 - x)) = _
  rw [show 204 = 50 +
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
  rw [recurrence4Scalar0Exceptional_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (204 + x) *
        remainder6Coefficient0.coeff (204 - (204 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 204 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (204 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (204 - (204 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_204 :
    recurrence4Scalar0Exceptional.coeff 204 =
      (((((69656248151324645211 * 10 ^ 70 +
        7213074996806843162289909106965188518183945635051029121563174225358823) * 10 ^ 70 +
        1004794373072345591602599468415497111819032045574475882510780537131722) * 10 ^ 70 +
        6065076111417076998704588884971884124162588446955700801726908102155590) * 10 ^ 70 +
        3862582058415700777341277529583499134238789202623560134662620724274505) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (204 - x)) = _
  rw [show 205 = 51 +
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
  rw [recurrence4Scalar0Exceptional_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (205 + x) *
        remainder6Coefficient0.coeff (205 - (205 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 205 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (205 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (205 - (205 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_205 :
    recurrence4Scalar0Exceptional.coeff 205 =
      -(((((145662205867588138312 * 10 ^ 70 +
        1544889301289169765823629781738050253760271289555218006635878451569354) * 10 ^ 70 +
        1221899074708020001449049699804100679624941698588205940072699331797112) * 10 ^ 70 +
        1388030019857019694949956442444311220278916354206974301409248462726894) * 10 ^ 70 +
        6041905232090805886146221266403166262858449404030623850417562151010940) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (205 - x)) = _
  rw [show 206 = 52 +
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
  rw [recurrence4Scalar0Exceptional_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (206 + x) *
        remainder6Coefficient0.coeff (206 - (206 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 206 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (206 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (206 - (206 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_206 :
    recurrence4Scalar0Exceptional.coeff 206 =
      (((((300316798183546859976 * 10 ^ 70 +
        1447826573402689158089466376318066702355062497729668689766181266069316) * 10 ^ 70 +
        6849287098910939993083940627926539572386963880551069772371500978152469) * 10 ^ 70 +
        6432410784127603146167105210304632856038166537483864605722665325528118) * 10 ^ 70 +
        3130216012480299057628917380024321108168143186916027583288477154663002) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (206 - x)) = _
  rw [show 207 = 53 +
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
  rw [recurrence4Scalar0Exceptional_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (207 + x) *
        remainder6Coefficient0.coeff (207 - (207 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 207 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (207 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (207 - (207 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_207 :
    recurrence4Scalar0Exceptional.coeff 207 =
      -(((((610495237946426500892 * 10 ^ 70 +
        3125281117875702625327068860194119766097850107317147429493223124161830) * 10 ^ 70 +
        5100473800356173676469577083285690387754962581826108435486964387878960) * 10 ^ 70 +
        2252065927481122419385706007113677554244204187062047425318640091447772) * 10 ^ 70 +
        8794739796285425561519222289990789343373015917645472995604279980344592) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (207 - x)) = _
  rw [show 208 = 54 +
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
  rw [recurrence4Scalar0Exceptional_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (208 + x) *
        remainder6Coefficient0.coeff (208 - (208 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 208 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (208 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (208 - (208 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_208 :
    recurrence4Scalar0Exceptional.coeff 208 =
      (((((1223708679782179571334 * 10 ^ 70 +
        0849948553568883771002194197337958875027033733301870223615509710677896) * 10 ^ 70 +
        6725783212932156447647286888284681260745514848922967797825242313195833) * 10 ^ 70 +
        2845508130487300436519861505325920159376433666842969797031030008978701) * 10 ^ 70 +
        5921799634073478786181368667882429103340561552522381515843686749283128) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (208 - x)) = _
  rw [show 209 = 55 +
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
  rw [recurrence4Scalar0Exceptional_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (209 + x) *
        remainder6Coefficient0.coeff (209 - (209 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 209 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (209 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (209 - (209 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_209 :
    recurrence4Scalar0Exceptional.coeff 209 =
      -(((((2418740865742487112066 * 10 ^ 70 +
        2032914584766447218250100871151962043879278484634054629109018718494012) * 10 ^ 70 +
        2235957949021359183271549293060673022017073956740927616676216304857973) * 10 ^ 70 +
        6063944475898432402404201698186377816708360731554982467454624844187843) * 10 ^ 70 +
        9022735779462921356233002954712538008240181262834996408195015382602220) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (209 - x)) = _
  rw [show 210 = 56 +
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
  rw [recurrence4Scalar0Exceptional_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (210 + x) *
        remainder6Coefficient0.coeff (210 - (210 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 210 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (210 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (210 - (210 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_210 :
    recurrence4Scalar0Exceptional.coeff 210 =
      (((((4714524504244204290364 * 10 ^ 70 +
        8484509301051020707808611974524210381164818527752431982119421274922601) * 10 ^ 70 +
        0306304392094179321123595487899769037941213728630277961975210654108629) * 10 ^ 70 +
        6439489821269248777825002720757761552266707975034425400908323390147039) * 10 ^ 70 +
        7937083443286794750429959658178160565649007336470520147309067142509225) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (210 - x)) = _
  rw [show 211 = 57 +
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
  rw [recurrence4Scalar0Exceptional_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (211 + x) *
        remainder6Coefficient0.coeff (211 - (211 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 211 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (211 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (211 - (211 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_211 :
    recurrence4Scalar0Exceptional.coeff 211 =
      -(((((9062431073655492206242 * 10 ^ 70 +
        1595057773037042286899611582140052410468896549100399387591264287731551) * 10 ^ 70 +
        7836739961522786181366755078653835584432885390639077345081830015610252) * 10 ^ 70 +
        9599317890439430421195453912401533037089163637890056113211387771753653) * 10 ^ 70 +
        9917877617712551719218150985014749012770790662971732758717591624808063) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (211 - x)) = _
  rw [show 212 = 58 +
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
  rw [recurrence4Scalar0Exceptional_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (212 + x) *
        remainder6Coefficient0.coeff (212 - (212 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 212 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (212 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (212 - (212 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_212 :
    recurrence4Scalar0Exceptional.coeff 212 =
      (((((17180275877190132745313 * 10 ^ 70 +
        3573046100639951875639614401729517327228398769297267633655200138193473) * 10 ^ 70 +
        8901625435908936356358276750702917384969121639420742151642761869112362) * 10 ^ 70 +
        3378721511777084005262163382320528130626961058011733019626214916276315) * 10 ^ 70 +
        3873098727353738616448997370856742371077731589859904973456681382494343) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (212 - x)) = _
  rw [show 213 = 59 +
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
  rw [recurrence4Scalar0Exceptional_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (213 + x) *
        remainder6Coefficient0.coeff (213 - (213 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 213 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (213 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (213 - (213 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_213 :
    recurrence4Scalar0Exceptional.coeff 213 =
      -(((((32122832065073475073777 * 10 ^ 70 +
        3259111534376489215494205552897180985732569235184680108675287512091173) * 10 ^ 70 +
        0452305966282153293076751040638627392662046187420527118356759607689557) * 10 ^ 70 +
        3554712745958686463328013813027695547115396344978566290015250811697563) * 10 ^ 70 +
        6932969232212478972321717267123915955639273381339046417532144153180308) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (213 - x)) = _
  rw [show 214 = 60 +
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
  rw [recurrence4Scalar0Exceptional_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (214 + x) *
        remainder6Coefficient0.coeff (214 - (214 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 214 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (214 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (214 - (214 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_214 :
    recurrence4Scalar0Exceptional.coeff 214 =
      (((((59239971884404161901093 * 10 ^ 70 +
        6686278345702904593620581153629978104633430311161517694360305654222058) * 10 ^ 70 +
        1063493012704740694661054584390723189392857682764243495512766271044346) * 10 ^ 70 +
        6181380225717528590161027353693175609844694900876418757767401279579408) * 10 ^ 70 +
        5064399083117597215480885344568362889914160780771914165447929841424271) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (214 - x)) = _
  rw [show 215 = 61 +
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
  rw [recurrence4Scalar0Exceptional_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (215 + x) *
        remainder6Coefficient0.coeff (215 - (215 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 215 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (215 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (215 - (215 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_215 :
    recurrence4Scalar0Exceptional.coeff 215 =
      -(((((107758519059204361154312 * 10 ^ 70 +
        8335396573673357364081983397829030611135961568461866174719160249364647) * 10 ^ 70 +
        0282761001302744932810118718205475543778674749786313029677007762509683) * 10 ^ 70 +
        2268302850321342125996322449765980597858578431990571504275542079447009) * 10 ^ 70 +
        5395760141489649059090345258852299489622161399096487030341807407447990) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (215 - x)) = _
  rw [show 216 = 62 +
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
  rw [recurrence4Scalar0Exceptional_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (216 + x) *
        remainder6Coefficient0.coeff (216 - (216 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 216 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (216 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (216 - (216 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_216 :
    recurrence4Scalar0Exceptional.coeff 216 =
      (((((193349019626962177810083 * 10 ^ 70 +
        1272287687823218929747147306885998687208498346564764283435931261713155) * 10 ^ 70 +
        0593393876238223936061753781010855545791780591078157604334078116679007) * 10 ^ 70 +
        4976140669437695276621909033177926338273055062380008749022221607228514) * 10 ^ 70 +
        6721706591774358320376624882671794614082467561501863545118447569053144) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (216 - x)) = _
  rw [show 217 = 63 +
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
  rw [recurrence4Scalar0Exceptional_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (217 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (217 + x) *
        remainder6Coefficient0.coeff (217 - (217 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 217 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (217 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (217 - (217 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_217 :
    recurrence4Scalar0Exceptional.coeff 217 =
      -(((((342218262046801429711379 * 10 ^ 70 +
        2453112606667863841166231073345999667137343905567243670713648763600433) * 10 ^ 70 +
        4724191419671727373112773004513090649501821658552325196846999840463140) * 10 ^ 70 +
        1557007479446865269172228278672812052398214515494744190063661166441727) * 10 ^ 70 +
        2683069919865651516279674394683682289021995204780135180939418521413159) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (217 - x)) = _
  rw [show 218 = 64 +
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
  rw [recurrence4Scalar0Exceptional_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (218 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (218 + x) *
        remainder6Coefficient0.coeff (218 - (218 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 218 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (218 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (218 - (218 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_218 :
    recurrence4Scalar0Exceptional.coeff 218 =
      (((((597519289990889381084091 * 10 ^ 70 +
        8507535535030519810310316572581339289488171942694621735788352020714654) * 10 ^ 70 +
        1194519140001285817348173317176284010555818993472731949769585327545482) * 10 ^ 70 +
        3064680043033628263183144689145039326338947157157304757088319247278849) * 10 ^ 70 +
        2851859680316178692503839075862703420994320829565713988855460142775547) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (218 - x)) = _
  rw [show 219 = 65 +
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
  rw [recurrence4Scalar0Exceptional_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (219 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (219 + x) *
        remainder6Coefficient0.coeff (219 - (219 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 219 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (219 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (219 - (219 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_219 :
    recurrence4Scalar0Exceptional.coeff 219 =
      -(((((1029210881588230251631279 * 10 ^ 70 +
        4442754598375687241802257229390810160720143622219707088222339892619262) * 10 ^ 70 +
        6198772456183622853575818934884511164693635110797276708029383870067806) * 10 ^ 70 +
        6813277603584276479011385879339846687399861633771843228056062291625203) * 10 ^ 70 +
        5756520495224724188199736271070980424441382792112939591003525516048788) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (219 - x)) = _
  rw [show 220 = 66 +
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
  rw [recurrence4Scalar0Exceptional_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (220 + x) *
        remainder6Coefficient0.coeff (220 - (220 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 220 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (220 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (220 - (220 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_220 :
    recurrence4Scalar0Exceptional.coeff 220 =
      (((((1748944843764138378861252 * 10 ^ 70 +
        1017131119299561982821524289230662075762171388114034967772966188272798) * 10 ^ 70 +
        8215138099984065006155832014744192077831391727258844561206355605939497) * 10 ^ 70 +
        1200508104318448215236888820347254199493707922370081202557385636420854) * 10 ^ 70 +
        8185841821396922699316522838385441986967781678428148446263154068626906) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (220 - x)) = _
  rw [show 221 = 67 +
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
  rw [recurrence4Scalar0Exceptional_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (221 + x) *
        remainder6Coefficient0.coeff (221 - (221 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 221 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (221 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (221 - (221 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_221 :
    recurrence4Scalar0Exceptional.coeff 221 =
      -(((((2932123503316514134197643 * 10 ^ 70 +
        1868879111684935747086698927721899191838686321480532098196539242127774) * 10 ^ 70 +
        3248014442059231890156860096304625463627112539711916194066635049269261) * 10 ^ 70 +
        5053899537351217765705311803396665381613105340216371813786304837049835) * 10 ^ 70 +
        9566424341063947279900371831560481928975993384819462988511804587983728) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (221 - x)) = _
  rw [show 222 = 68 +
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
  rw [recurrence4Scalar0Exceptional_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (222 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (222 + x) *
        remainder6Coefficient0.coeff (222 - (222 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 222 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (222 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (222 - (222 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_222 :
    recurrence4Scalar0Exceptional.coeff 222 =
      (((((4849951510471557501658122 * 10 ^ 70 +
        0418584546241052158056869758524358158525145869334608770580680100327132) * 10 ^ 70 +
        1860904814285606106110775731208239013150547564844273661867168877153862) * 10 ^ 70 +
        1339901204248123167300041572269748492950094349848752912149885371588153) * 10 ^ 70 +
        6706627288400944158556087379802749126044827148601024000712399119551182) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (222 - x)) = _
  rw [show 223 = 69 +
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
  rw [recurrence4Scalar0Exceptional_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (223 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (223 + x) *
        remainder6Coefficient0.coeff (223 - (223 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 223 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (223 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (223 - (223 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_223 :
    recurrence4Scalar0Exceptional.coeff 223 =
      -(((((7915085697569532038145749 * 10 ^ 70 +
        3653199698729850341036965382693665803865007884634446224100151457355729) * 10 ^ 70 +
        0350763808588096050949340800960073855672818834631614959776473098314499) * 10 ^ 70 +
        0361291387749572402907705220814640410810243548112020328332178541245635) * 10 ^ 70 +
        0389283906428889538376128824317479156329343418011500409235441576331162) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (223 - x)) = _
  rw [show 224 = 70 +
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
  rw [recurrence4Scalar0Exceptional_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (224 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (224 + x) *
        remainder6Coefficient0.coeff (224 - (224 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 224 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (224 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (224 - (224 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_224 :
    recurrence4Scalar0Exceptional.coeff 224 =
      (((((12745314207245562381171801 * 10 ^ 70 +
        7387378880551148670618580986476676301028293131308501061743150618217192) * 10 ^ 70 +
        6178453985616415655814923399330556146792850379382736883319475329768062) * 10 ^ 70 +
        6292817288529494506544039215294935038682940490409284835691036756713487) * 10 ^ 70 +
        3194193128080313100439236743194597791668288048719536043856824122873972) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (224 - x)) = _
  rw [show 225 = 71 +
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
  rw [recurrence4Scalar0Exceptional_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (225 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (225 + x) *
        remainder6Coefficient0.coeff (225 - (225 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 225 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (225 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (225 - (225 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_225 :
    recurrence4Scalar0Exceptional.coeff 225 =
      -(((((20250479573652379668568648 * 10 ^ 70 +
        8230130452994135838430409480195742018920365356430194420351499282727634) * 10 ^ 70 +
        4883400165117278334163750977559295738019454022802743439444221290511995) * 10 ^ 70 +
        3277916200033344455634406110637167305820367954726645831284581568277145) * 10 ^ 70 +
        9705393780953817007063741977505462064113129608169406274390954084632909) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (225 - x)) = _
  rw [show 226 = 72 +
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
  rw [recurrence4Scalar0Exceptional_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (226 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (226 + x) *
        remainder6Coefficient0.coeff (226 - (226 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 226 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (226 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (226 - (226 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_226 :
    recurrence4Scalar0Exceptional.coeff 226 =
      (((((31748455213473260906110695 * 10 ^ 70 +
        8592931292013784429348212409932561867226825676386022537713310898654689) * 10 ^ 70 +
        1423432156139021828306597959433208518305773614324726854699213989918284) * 10 ^ 70 +
        6713984421170240607356809655297707162789217337252797123883036434836190) * 10 ^ 70 +
        8923942645028613352583701613711796930364997623786432079362070792294095) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (226 - x)) = _
  rw [show 227 = 73 +
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
  rw [recurrence4Scalar0Exceptional_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (227 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (227 + x) *
        remainder6Coefficient0.coeff (227 - (227 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 227 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (227 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (227 - (227 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_227 :
    recurrence4Scalar0Exceptional.coeff 227 =
      -(((((49116185477827074891174511 * 10 ^ 70 +
        2381020058133144716632347075833166745601437837878046729757576372218603) * 10 ^ 70 +
        2098667078713210388706321450574699173560836516258342975476649304634459) * 10 ^ 70 +
        4605678668164511666720283471467910354001896615696718542826751025675408) * 10 ^ 70 +
        3733874476440819434854350843538970061204425513358617984980934545563504) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (227 - x)) = _
  rw [show 228 = 74 +
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
  rw [recurrence4Scalar0Exceptional_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (228 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (228 + x) *
        remainder6Coefficient0.coeff (228 - (228 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 228 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (228 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (228 - (228 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_228 :
    recurrence4Scalar0Exceptional.coeff 228 =
      (((((74981339019091272804492539 * 10 ^ 70 +
        8186957485758148249987530866574988351689678579778275610836553272359816) * 10 ^ 70 +
        2277892412782767191299052472491114842585466062568054619589207300868092) * 10 ^ 70 +
        4391652917300433779157224867013072540177738384799447410233551232154143) * 10 ^ 70 +
        1957937859272603353804716054699355428384116317691240537577033528339990) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (228 - x)) = _
  rw [show 229 = 75 +
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
  rw [recurrence4Scalar0Exceptional_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (229 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (229 + x) *
        remainder6Coefficient0.coeff (229 - (229 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 229 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (229 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (229 - (229 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_229 :
    recurrence4Scalar0Exceptional.coeff 229 =
      -(((((112958685510429676467284217 * 10 ^ 70 +
        7948178947463629039537265821620135854442772708429782740557021430230285) * 10 ^ 70 +
        8304622933250707040017218636870537483830783555931370582851550075878673) * 10 ^ 70 +
        2933779810034401150298048760215452448305534462019305631656189713827871) * 10 ^ 70 +
        0581988530674148200492053717418989927422812703922748659939627935666011) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (229 - x)) = _
  rw [show 230 = 76 +
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
  rw [recurrence4Scalar0Exceptional_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (230 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (230 + x) *
        remainder6Coefficient0.coeff (230 - (230 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 230 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (230 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (230 - (230 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_230 :
    recurrence4Scalar0Exceptional.coeff 230 =
      (((((167932543642172697405405256 * 10 ^ 70 +
        2959336850484243300544575372627804142766062204324780875268192206232313) * 10 ^ 70 +
        9264472682375867226069112107476015870075453463080891044290117318055879) * 10 ^ 70 +
        7389282673476033373005062012455112313105069581365836442194822918074915) * 10 ^ 70 +
        5014756642544000714618305650158978304667443693193853437214024544900141) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (230 - x)) = _
  rw [show 231 = 77 +
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
  rw [recurrence4Scalar0Exceptional_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (231 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (231 + x) *
        remainder6Coefficient0.coeff (231 - (231 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 231 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (231 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (231 - (231 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_231 :
    recurrence4Scalar0Exceptional.coeff 231 =
      -(((((246382241921825864732584465 * 10 ^ 70 +
        1083655657426079033797191226065100323097276829590692545225921464119639) * 10 ^ 70 +
        5235894431673091922311332448368327695355419345843785065668456695839864) * 10 ^ 70 +
        8544829998128148378936613372532801502785046065779024841522860107959562) * 10 ^ 70 +
        9535302457283688754048423480788057411271620715370117625449413629320112) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (231 - x)) = _
  rw [show 232 = 78 +
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
  rw [recurrence4Scalar0Exceptional_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (232 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (232 + x) *
        remainder6Coefficient0.coeff (232 - (232 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 232 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (232 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (232 - (232 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_232 :
    recurrence4Scalar0Exceptional.coeff 232 =
      (((((356741249631187880534246952 * 10 ^ 70 +
        4243895153752174001548153203769691409873060413322906901546004687689566) * 10 ^ 70 +
        4740446931290248932055096151673540505068726773996978729447524861629889) * 10 ^ 70 +
        4574393005552266442326788441992040838568170620908986942602934332021026) * 10 ^ 70 +
        4336684364611148007101233492022425844776937659876624532530758638409174) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (232 - x)) = _
  rw [show 233 = 79 +
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
  rw [recurrence4Scalar0Exceptional_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (233 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (233 + x) *
        remainder6Coefficient0.coeff (233 - (233 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 233 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (233 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (233 - (233 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_233 :
    recurrence4Scalar0Exceptional.coeff 233 =
      -(((((509772414258623222876154882 * 10 ^ 70 +
        0674591325818686865678244470239991067329286633811503542227687161185698) * 10 ^ 70 +
        7609608843338427076890320813265495169493623442244371679892439605938017) * 10 ^ 70 +
        9806672944889617115609106358672832800853163976269430971461600120935797) * 10 ^ 70 +
        5195849378641639497855471286767302655148144294324250420398422871666401) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (233 - x)) = _
  rw [show 234 = 80 +
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
  rw [recurrence4Scalar0Exceptional_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (234 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (234 + x) *
        remainder6Coefficient0.coeff (234 - (234 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 234 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (234 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (234 - (234 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_234 :
    recurrence4Scalar0Exceptional.coeff 234 =
      (((((718931796295463724506860587 * 10 ^ 70 +
        3963914070783016623899448749001610711108236030231811218656982198567337) * 10 ^ 70 +
        3811011762578727898779271068643428268885640468460140769736526660329614) * 10 ^ 70 +
        2636574639022996857897181103923824578807828250195261430014319896953971) * 10 ^ 70 +
        6841492360331401377094126126895535659466283936122972609869721644333916) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (234 - x)) = _
  rw [show 235 = 81 +
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
  rw [recurrence4Scalar0Exceptional_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (235 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (235 + x) *
        remainder6Coefficient0.coeff (235 - (235 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 235 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (235 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (235 - (235 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_235 :
    recurrence4Scalar0Exceptional.coeff 235 =
      -(((((1000682500825174777235268458 * 10 ^ 70 +
        6802637980643945565210018978669613425420805369117805393660004539867773) * 10 ^ 70 +
        7695184009815764465225211484088749333597688952858053213839887909040599) * 10 ^ 70 +
        6835139509542778423417337687189661131224685740396096948332969725202719) * 10 ^ 70 +
        3799413643793696284984997757710600513026720869351547476147875298819760) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (235 - x)) = _
  rw [show 236 = 82 +
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
  rw [recurrence4Scalar0Exceptional_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (236 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (236 + x) *
        remainder6Coefficient0.coeff (236 - (236 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 236 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (236 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (236 - (236 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_236 :
    recurrence4Scalar0Exceptional.coeff 236 =
      (((((1374708683517134056093269694 * 10 ^ 70 +
        4271493213440038466606836923189749946732072666007058699443212057224500) * 10 ^ 70 +
        2546079033928613360159702758869046447583135651919899075901839375085516) * 10 ^ 70 +
        3850159128708318874412424168997758823506045979460414037686787457258123) * 10 ^ 70 +
        3307083541263914039064741151899751458627242768852912614440292750882016) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (236 - x)) = _
  rw [show 237 = 83 +
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
  rw [recurrence4Scalar0Exceptional_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (237 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (237 + x) *
        remainder6Coefficient0.coeff (237 - (237 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 237 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (237 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (237 - (237 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_237 :
    recurrence4Scalar0Exceptional.coeff 237 =
      -(((((1863970033335991839534833536 * 10 ^ 70 +
        0999377531747497763120237656490316958355733157549031149592052403753211) * 10 ^ 70 +
        9903030830925396557667345536042839007161756948952389714182853277513621) * 10 ^ 70 +
        0535670023250713678014997281283704452225980699366313755737556681501178) * 10 ^ 70 +
        4453761980391560604696825652737185127376117876176267885401637465973136) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (237 - x)) = _
  rw [show 238 = 84 +
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
  rw [recurrence4Scalar0Exceptional_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (238 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (238 + x) *
        remainder6Coefficient0.coeff (238 - (238 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 238 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (238 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (238 - (238 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_238 :
    recurrence4Scalar0Exceptional.coeff 238 =
      (((((2494530394319654884984877010 * 10 ^ 70 +
        5250820167810817299454807116843299433505369578258314504156252237805288) * 10 ^ 70 +
        5078807459068937513452143189031793652889474838991524790331833132905232) * 10 ^ 70 +
        7921927881039950615325251617166843691237638408593865297125795566085124) * 10 ^ 70 +
        0869714312266339224151964943281430619381252628371622154778014717338633) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (238 - x)) = _
  rw [show 239 = 85 +
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
  rw [recurrence4Scalar0Exceptional_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (239 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (239 + x) *
        remainder6Coefficient0.coeff (239 - (239 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 239 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (239 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (239 - (239 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_239 :
    recurrence4Scalar0Exceptional.coeff 239 =
      -(((((3295092941322384725078356515 * 10 ^ 70 +
        2341491170411775924246413737906236084313674911948688302090659501417319) * 10 ^ 70 +
        8303289922752898637388479401028234804279376640460550717608626506735659) * 10 ^ 70 +
        8795281251397445983497119983790455542564096968058256834759996644493145) * 10 ^ 70 +
        7145275254335473437785826293247681952833640178114476046156415281975319) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (239 - x)) = _
  rw [show 240 = 86 +
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
  rw [recurrence4Scalar0Exceptional_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (240 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (240 + x) *
        remainder6Coefficient0.coeff (240 - (240 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 240 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (240 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (240 - (240 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_240 :
    recurrence4Scalar0Exceptional.coeff 240 =
      (((((4296180646802707331862979447 * 10 ^ 70 +
        9200539902413608229654472866505873091638611767029546951782054362070697) * 10 ^ 70 +
        4165038033864161565998727804464004724819174873864414335655951463895446) * 10 ^ 70 +
        3718595185459736378801155630375980226807443308626843424055120794317188) * 10 ^ 70 +
        6437064516244561900910592847776939732786248454989550388665000579408158) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (240 - x)) = _
  rw [show 241 = 87 +
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
  rw [recurrence4Scalar0Exceptional_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (241 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (241 + x) *
        remainder6Coefficient0.coeff (241 - (241 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 241 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (241 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (241 - (241 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_241 :
    recurrence4Scalar0Exceptional.coeff 241 =
      -(((((5528916518824874957635508242 * 10 ^ 70 +
        8756722350499549848736169962170655079659037894813234194823507917348732) * 10 ^ 70 +
        5201987696434789717148447756482087786124898590151875005907450980090796) * 10 ^ 70 +
        0504987467950381612746303270218701758559858282986838312004527344485967) * 10 ^ 70 +
        6294418169356708133790799786664713364391569880812580637257723613476449) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (241 - x)) = _
  rw [show 242 = 88 +
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
  rw [recurrence4Scalar0Exceptional_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (242 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (242 + x) *
        remainder6Coefficient0.coeff (242 - (242 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 242 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (242 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (242 - (242 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_242 :
    recurrence4Scalar0Exceptional.coeff 242 =
      (((((7023384366436448349307271143 * 10 ^ 70 +
        2833948965985507502102980711199337223601733707669306683340490666310351) * 10 ^ 70 +
        8359245106307820899514338718526927375028012448849466698824311771194848) * 10 ^ 70 +
        4415740785509146018691290378947484915496050196621856850492117403013931) * 10 ^ 70 +
        5471596838901946891989101153368940495406461175032169466743219715908384) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (242 - x)) = _
  rw [show 243 = 89 +
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
  rw [recurrence4Scalar0Exceptional_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (243 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (243 + x) *
        remainder6Coefficient0.coeff (243 - (243 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 243 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (243 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (243 - (243 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_243 :
    recurrence4Scalar0Exceptional.coeff 243 =
      -(((((8806587603753488617443967942 * 10 ^ 70 +
        8812157807033352734241340781066010480843599546491113545215286688381779) * 10 ^ 70 +
        7228334158211194712599950399835040317694751925546365538183094340140197) * 10 ^ 70 +
        8631261850538413214030813221389825114384516025586976785395810280932203) * 10 ^ 70 +
        6939410234672542193694577650158361520839483326648285160096886915873346) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (243 - x)) = _
  rw [show 244 = 90 +
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
  rw [recurrence4Scalar0Exceptional_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (244 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (244 + x) *
        remainder6Coefficient0.coeff (244 - (244 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 244 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (244 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (244 - (244 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_244 :
    recurrence4Scalar0Exceptional.coeff 244 =
      (((((10900069255185865446079832877 * 10 ^ 70 +
        9224568833721346698679269471927727383084607856161819473182528679696554) * 10 ^ 70 +
        2836757111595748408598078453279012175880130511641799064091063539248342) * 10 ^ 70 +
        8596781551428722056410164459356563233482780996746736290336109865716663) * 10 ^ 70 +
        3485054819854035675435263689718849915617538969818623262919450569494646) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (244 - x)) = _
  rw [show 245 = 91 +
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
  rw [recurrence4Scalar0Exceptional_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (245 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (245 + x) *
        remainder6Coefficient0.coeff (245 - (245 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 245 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (245 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (245 - (245 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_245 :
    recurrence4Scalar0Exceptional.coeff 245 =
      -(((((13317307545172335108369262909 * 10 ^ 70 +
        7549307482351044323789493916528662003555337858996756828317458239197958) * 10 ^ 70 +
        0314636104309972888150221829096436483196228026641804783065974436209982) * 10 ^ 70 +
        7657690834044548734134014327545758139773869484169931470296527234289754) * 10 ^ 70 +
        2260495520219225876413797480366621545703429600540601766564664018950840) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (245 - x)) = _
  rw [show 246 = 92 +
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
  rw [recurrence4Scalar0Exceptional_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (246 + x) *
        remainder6Coefficient0.coeff (246 - (246 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 246 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (246 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (246 - (246 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_246 :
    recurrence4Scalar0Exceptional.coeff 246 =
      (((((16061053199542371936135289300 * 10 ^ 70 +
        2199010509631207627436228262669196081275320721571679332742126131789722) * 10 ^ 70 +
        4642415556321059230760934995265200844107754479484221933925637821333101) * 10 ^ 70 +
        6338153698902103216218817278809811166003882532083430289952640489053693) * 10 ^ 70 +
        7521981029894209979623043239515998529503694001074057336371155877063891) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (246 - x)) = _
  rw [show 247 = 93 +
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
  rw [recurrence4Scalar0Exceptional_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (247 + x) *
        remainder6Coefficient0.coeff (247 - (247 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 247 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (247 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (247 - (247 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_247 :
    recurrence4Scalar0Exceptional.coeff 247 =
      -(((((19120820404375514924505787785 * 10 ^ 70 +
        6088975408466829665598600034116145542472683025637302412466378281523109) * 10 ^ 70 +
        6191048364022662787550349123803416120822703865503547084073845859956256) * 10 ^ 70 +
        7716958144630465021628944838836272849211174592955342938708668639712450) * 10 ^ 70 +
        5830918195393949570799764898489395495068630503238786324650772668177683) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (247 - x)) = _
  rw [show 248 = 94 +
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
  rw [recurrence4Scalar0Exceptional_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (248 + x) *
        remainder6Coefficient0.coeff (248 - (248 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 248 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (248 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (248 - (248 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_248 :
    recurrence4Scalar0Exceptional.coeff 248 =
      (((((22470776053431765725217464846 * 10 ^ 70 +
        1820061626109042733549845819578170336886610594904593691865372479791796) * 10 ^ 70 +
        8987089197891366171134628870435814662355848881907561814445755844267876) * 10 ^ 70 +
        3857179595220891759492964721656154810946329694110965886583055235877013) * 10 ^ 70 +
        6214978828170343330926793192257186759294386666556010780161877526470817) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (248 - x)) = _
  rw [show 249 = 95 +
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
  rw [recurrence4Scalar0Exceptional_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (249 + x) *
        remainder6Coefficient0.coeff (249 - (249 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 249 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (249 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (249 - (249 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_249 :
    recurrence4Scalar0Exceptional.coeff 249 =
      -(((((26068284422203083022731341125 * 10 ^ 70 +
        5131350457199786135909233646607868466111649688831224778965223891057739) * 10 ^ 70 +
        9807895212359173011990203518977477585829446434571973001772440205229815) * 10 ^ 70 +
        2644817083353366403665862478298494622625698408929468807897529526149851) * 10 ^ 70 +
        9302403774317587629910830174443727646555280762141737003089843868978209) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (249 - x)) = _
  rw [show 250 = 96 +
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
  rw [recurrence4Scalar0Exceptional_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (250 + x) *
        remainder6Coefficient0.coeff (250 - (250 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 250 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (250 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (250 - (250 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_250 :
    recurrence4Scalar0Exceptional.coeff 250 =
      (((((29853350964705157507266812435 * 10 ^ 70 +
        2708627324497920914425392070930953090433713120769034960362327021804151) * 10 ^ 70 +
        8030374432789763929738081565508288394518310791443930106529957655148908) * 10 ^ 70 +
        7734241996784297601552529247589877278758303492597885897932286171442384) * 10 ^ 70 +
        5631271995491591027518412348787353862272407373969080524523881436332262) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (250 - x)) = _
  rw [show 251 = 97 +
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
  rw [recurrence4Scalar0Exceptional_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (251 + x) *
        remainder6Coefficient0.coeff (251 - (251 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 251 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (251 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (251 - (251 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_251 :
    recurrence4Scalar0Exceptional.coeff 251 =
      -(((((33749166179600488319765853402 * 10 ^ 70 +
        9828946406116474435021230913102412205815522769208426496484237312565626) * 10 ^ 70 +
        7275256394196789405974875285470767431569279643787058445398244925548804) * 10 ^ 70 +
        8880768759234155557298658780126474913067698126394538646975994949789265) * 10 ^ 70 +
        0599187005838119500317881205074039609078349093644574201698091735714619) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (251 - x)) = _
  rw [show 252 = 98 +
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
  rw [recurrence4Scalar0Exceptional_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (252 + x) *
        remainder6Coefficient0.coeff (252 - (252 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 252 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (252 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (252 - (252 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_252 :
    recurrence4Scalar0Exceptional.coeff 252 =
      (((((37663878457715776351005170131 * 10 ^ 70 +
        1906864133139674038055454277838718402998808483614138510196078093506459) * 10 ^ 70 +
        4544090781510290993620376684246647687899949642304670043822854392483744) * 10 ^ 70 +
        7760303512523518074138972300515445510877920374214358067752365852182049) * 10 ^ 70 +
        9558667980088224015259270834983689820606889246265116659337647767584426) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (252 - x)) = _
  rw [show 253 = 99 +
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
  rw [recurrence4Scalar0Exceptional_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (253 + x) *
        remainder6Coefficient0.coeff (253 - (253 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 253 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (253 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (253 - (253 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_253 :
    recurrence4Scalar0Exceptional.coeff 253 =
      -(((((41493627504468658799736636557 * 10 ^ 70 +
        4081587338833737324646904838108976229847807986505011174412852105965043) * 10 ^ 70 +
        9413262803993937746881891450323157137342484594112084039086461767562029) * 10 ^ 70 +
        0367906941981905764785963516818985161183106483137336370881611934158281) * 10 ^ 70 +
        1086237182252084824090316853558756296896227087506278046274738537432729) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (253 - x)) = _
  rw [show 254 = 100 +
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
  rw [recurrence4Scalar0Exceptional_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (254 + x) *
        remainder6Coefficient0.coeff (254 - (254 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 254 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (254 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (254 - (254 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_254 :
    recurrence4Scalar0Exceptional.coeff 254 =
      (((((45126755361900232808404666082 * 10 ^ 70 +
        4901729579712259547870845746044946054943043126590823035626748315203084) * 10 ^ 70 +
        5462535304113795633176616320379480159077425424136862091249057158921257) * 10 ^ 70 +
        9067832337561035943496505193448001273923277632173533299984395939381324) * 10 ^ 70 +
        5056166311279754037607703474748476779335983775586314984572884739806225) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (254 - x)) = _
  rw [show 255 = 101 +
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
  rw [recurrence4Scalar0Exceptional_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (255 + x) *
        remainder6Coefficient0.coeff (255 - (255 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 255 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (255 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (255 - (255 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_255 :
    recurrence4Scalar0Exceptional.coeff 255 =
      -(((((48448991716717390836629283196 * 10 ^ 70 +
        8793842409483963567507604517622173780493487739867607888423313082167336) * 10 ^ 70 +
        4818372125734452436854590651851426808454106285888975686480426990334099) * 10 ^ 70 +
        6199443045813834246716808062083018830829340798868011383432897026553535) * 10 ^ 70 +
        9223818980520446982611389510646606796638499087743973631059251961143661) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (255 - x)) = _
  rw [show 256 = 102 +
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
  rw [recurrence4Scalar0Exceptional_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (256 + x) *
        remainder6Coefficient0.coeff (256 - (256 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 256 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (256 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (256 - (256 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_256 :
    recurrence4Scalar0Exceptional.coeff 256 =
      (((((51349297781953758254991772608 * 10 ^ 70 +
        0529889059009742835729049134000651425699866739092324265138860222316169) * 10 ^ 70 +
        5519567274954948953988510504010597115536384597183258318360761018451412) * 10 ^ 70 +
        6817292073743147061328525527579793509988558870894810093796422682987073) * 10 ^ 70 +
        6106448165958143711108600974750142707691913082674775702130872258911998) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (256 - x)) = _
  rw [show 257 = 103 +
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
  rw [recurrence4Scalar0Exceptional_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (257 + x) *
        remainder6Coefficient0.coeff (257 - (257 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 257 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (257 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (257 - (257 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_257 :
    recurrence4Scalar0Exceptional.coeff 257 =
      -(((((53725962790937846061941284314 * 10 ^ 70 +
        9443147550763628832655688487085255980785046629886057886881626247888070) * 10 ^ 70 +
        3910954938128405088862115701756911135972753234772815312800483314660271) * 10 ^ 70 +
        2293412507486073582412904615411633731286635909583648382353473931643169) * 10 ^ 70 +
        7592964865309058664637724210742821559981456834434503424835203799195946) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (257 - x)) = _
  rw [show 258 = 104 +
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
  rw [recurrence4Scalar0Exceptional_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (258 + x) *
        remainder6Coefficient0.coeff (258 - (258 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 258 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (258 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (258 - (258 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_258 :
    recurrence4Scalar0Exceptional.coeff 258 =
      (((((55492491754861138264403019579 * 10 ^ 70 +
        8246558766266377754031893037081894130270378531211474785567168735532927) * 10 ^ 70 +
        1674877274333108094488083638418585591099244852102684544819262270206972) * 10 ^ 70 +
        8703332553405636373787716651624289918102252598407193999983065270533401) * 10 ^ 70 +
        2440608495010304464741957938175982883755562006301141329305438366325603) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (258 - x)) = _
  rw [show 259 = 105 +
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
  rw [recurrence4Scalar0Exceptional_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (259 + x) *
        remainder6Coefficient0.coeff (259 - (259 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 259 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (259 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (259 - (259 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_259 :
    recurrence4Scalar0Exceptional.coeff 259 =
      -(((((56582811859564703728827517149 * 10 ^ 70 +
        0921544087476231587438555644729884659703462014034467448865949306586600) * 10 ^ 70 +
        0294718834135464765879710534947378787431884315967819931342171833023931) * 10 ^ 70 +
        6267529770007582126913728664754380134890298300042940883486159677622166) * 10 ^ 70 +
        3314260230549195811804438001495652200306532596203212873391125317139598) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (259 - x)) = _
  rw [show 260 = 106 +
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
  rw [recurrence4Scalar0Exceptional_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (260 + x) *
        remainder6Coefficient0.coeff (260 - (260 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 260 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (260 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (260 - (260 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_260 :
    recurrence4Scalar0Exceptional.coeff 260 =
      (((((56955361911137408257858548807 * 10 ^ 70 +
        8106979806732175767596032841057592826577031182907351627775768598858906) * 10 ^ 70 +
        5979686025197230845756773734417924910522156420644391405344527344831449) * 10 ^ 70 +
        5445452296483282562543570926443936924303252356499402405294872374003611) * 10 ^ 70 +
        9594468097097287342291709008715481690859972800360227281618793223418223) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (260 - x)) = _
  rw [show 261 = 107 +
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
  rw [recurrence4Scalar0Exceptional_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (261 + x) *
        remainder6Coefficient0.coeff (261 - (261 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 261 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (261 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (261 - (261 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_261 :
    recurrence4Scalar0Exceptional.coeff 261 =
      -(((((56595712805915794536084223109 * 10 ^ 70 +
        9146702971263001521357737854578359402280642738319260607714281501687823) * 10 ^ 70 +
        0575909917512518333165275262303817174109383232009651297376062490377073) * 10 ^ 70 +
        0162609641743620516719969377216355464248059736035994985263580135106893) * 10 ^ 70 +
        6115660540889143820800532080563516751575233240614993117205147809727607) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (261 - x)) = _
  rw [show 262 = 108 +
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
  rw [recurrence4Scalar0Exceptional_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (262 + x) *
        remainder6Coefficient0.coeff (262 - (262 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 262 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (262 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (262 - (262 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_262 :
    recurrence4Scalar0Exceptional.coeff 262 =
      (((((55517489286479726939782034485 * 10 ^ 70 +
        5365358321561892424699987598500436987519368651917290826955058339258425) * 10 ^ 70 +
        4631049011729903183572842547952580918620107097736282386930652335922896) * 10 ^ 70 +
        8444848656880163274574569445151983887583939852775920303426690643196641) * 10 ^ 70 +
        2906683073328093412684090561869372989544426848333000946697669701327492) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (262 - x)) = _
  rw [show 263 = 109 +
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
  rw [recurrence4Scalar0Exceptional_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (263 + x) *
        remainder6Coefficient0.coeff (263 - (263 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 263 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (263 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (263 - (263 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_263 :
    recurrence4Scalar0Exceptional.coeff 263 =
      -(((((53761511264666791087361408742 * 10 ^ 70 +
        1229044293231516350074215093365745604200869985031649984294105018243593) * 10 ^ 70 +
        6819942730552291195633050184601020668032080416291685087403588564613581) * 10 ^ 70 +
        6915423106371118905122882062510945633271517233861063145198694928898311) * 10 ^ 70 +
        0881411607567337023267146937457754866530471484273928998923648141661950) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (263 - x)) = _
  rw [show 264 = 110 +
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
  rw [recurrence4Scalar0Exceptional_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (264 + x) *
        remainder6Coefficient0.coeff (264 - (264 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 264 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (264 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (264 - (264 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_264 :
    recurrence4Scalar0Exceptional.coeff 264 =
      (((((51393230256734765448274090894 * 10 ^ 70 +
        7615979383156640237334282386627154732688607324276898327099100849049681) * 10 ^ 70 +
        9860503527548467228905365169994068020987053549132684097485557028859724) * 10 ^ 70 +
        9533738383494222056128561983597490037883559588841045365851578713360445) * 10 ^ 70 +
        3712362201856259908400558703456161323235772649125572867131214090718129) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (264 - x)) = _
  rw [show 265 = 111 +
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
  rw [recurrence4Scalar0Exceptional_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (265 + x) *
        remainder6Coefficient0.coeff (265 - (265 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 265 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (265 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (265 - (265 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_265 :
    recurrence4Scalar0Exceptional.coeff 265 =
      -(((((48498685226167493232205024622 * 10 ^ 70 +
        4657411023059970409720874259215201782484424600637552001423345868137433) * 10 ^ 70 +
        9155712693681773179713819322076059385522496655325487127093829311554935) * 10 ^ 70 +
        7272958950494620311773181052429546896383217588225923936357532588871640) * 10 ^ 70 +
        1157756204959475509451527129895722306925086323516350286432338971705781) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (265 - x)) = _
  rw [show 266 = 112 +
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
  rw [recurrence4Scalar0Exceptional_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (266 + x) *
        remainder6Coefficient0.coeff (266 - (266 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 266 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (266 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (266 - (266 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_266 :
    recurrence4Scalar0Exceptional.coeff 266 =
      (((((45179325775472809401177006469 * 10 ^ 70 +
        7687973259525090542305366557216648786429077806067484460520115049140250) * 10 ^ 70 +
        9466759694033691535636544884075118934116934800234006292876256990329943) * 10 ^ 70 +
        2367359986953271306361894172870822653021703110678143290658054648617687) * 10 ^ 70 +
        4957842142718646405904372421597566016132658162390954520355278276507987) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (266 - x)) = _
  rw [show 267 = 113 +
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
  rw [recurrence4Scalar0Exceptional_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (267 + x) *
        remainder6Coefficient0.coeff (267 - (267 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 267 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (267 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (267 - (267 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_267 :
    recurrence4Scalar0Exceptional.coeff 267 =
      -(((((41546135995492273928455368182 * 10 ^ 70 +
        3055509650135341753483812251293704481475440636330953774262908708267489) * 10 ^ 70 +
        2670363729851377193494135310067470062229981055809000545336468577591373) * 10 ^ 70 +
        6354221469477599771969127833302823377398367673920310551134944738944924) * 10 ^ 70 +
        6024128874075747067906448460463967836918001829057748749108825854992375) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (267 - x)) = _
  rw [show 268 = 114 +
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
  rw [recurrence4Scalar0Exceptional_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (268 + x) *
        remainder6Coefficient0.coeff (268 - (268 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 268 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (268 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (268 - (268 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_268 :
    recurrence4Scalar0Exceptional.coeff 268 =
      (((((37713531313966814122575673171 * 10 ^ 70 +
        4922456138033326279128848266163437132958345817380944692277930910282115) * 10 ^ 70 +
        3530435164007933250808055739983181532549345870362909743165677155866326) * 10 ^ 70 +
        6060259744105572174853562465289541787125017959961737342622200329596049) * 10 ^ 70 +
        0312378758493768339252157796164355415279717607714150784492241036463792) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (268 - x)) = _
  rw [show 269 = 115 +
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
  rw [recurrence4Scalar0Exceptional_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (269 + x) *
        remainder6Coefficient0.coeff (269 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 269 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (269 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (269 - (269 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_269 :
    recurrence4Scalar0Exceptional.coeff 269 =
      -(((((33793491345758490500621165721 * 10 ^ 70 +
        0988162970947184655193506137622131909837929518714096407487066144325907) * 10 ^ 70 +
        1049421077055591666096550021490592969496221145828870061070251946345356) * 10 ^ 70 +
        6599045431496555332043747406454819848688950153495502426490936389526136) * 10 ^ 70 +
        1867006054438364463757993348192522751767219924942976125308599001775247) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (269 - x)) = _
  rw [show 270 = 116 +
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
  rw [recurrence4Scalar0Exceptional_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (270 + x) *
        remainder6Coefficient0.coeff (270 - (270 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 270 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (270 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (270 - (270 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_270 :
    recurrence4Scalar0Exceptional.coeff 270 =
      (((((29890337993614329757060212856 * 10 ^ 70 +
        0583581359202348571940006348027636463604673745155761432848230206746736) * 10 ^ 70 +
        4337649189831675307765426304396248854644745769248339816953387428942072) * 10 ^ 70 +
        0750834136075914097487858829063386858394053891245255522481204893214637) * 10 ^ 70 +
        0973143392899356221364899825357104086830723989585596253058204905779264) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (270 - x)) = _
  rw [show 271 = 117 +
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
  rw [recurrence4Scalar0Exceptional_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Exceptional_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C0_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Exceptional_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (271 + x) *
        remainder6Coefficient0.coeff (271 - (271 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 271 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (271 + x) hleft]
    norm_num
  · rw [recurrence4C0_coeff_low
      (271 - (271 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Exceptional_coeff_271 :
    recurrence4Scalar0Exceptional.coeff 271 =
      -(((((26096478946643942846693922998 * 10 ^ 70 +
        6826928761455313701453059600283687938923074790833048877129875146188401) * 10 ^ 70 +
        2410628859418307012785490493478734790312526755185869596538013520157502) * 10 ^ 70 +
        5312918969063085802530471327810413035111656586627930725777691197791352) * 10 ^ 70 +
        6713497138000646271822537319159035701141919006490570877965404226538910) : ℚ) := by
  unfold recurrence4Scalar0Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient0.coeff (271 - x)) = _
  rw [show 272 = 118 +
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
  rw [recurrence4Scalar0Exceptional_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Exceptional_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
