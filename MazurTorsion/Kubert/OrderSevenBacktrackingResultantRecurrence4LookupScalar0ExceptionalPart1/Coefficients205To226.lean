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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
