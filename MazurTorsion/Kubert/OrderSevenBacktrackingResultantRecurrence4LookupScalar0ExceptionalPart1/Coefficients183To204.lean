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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
