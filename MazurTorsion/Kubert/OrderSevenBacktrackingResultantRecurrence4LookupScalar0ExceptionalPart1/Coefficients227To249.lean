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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
