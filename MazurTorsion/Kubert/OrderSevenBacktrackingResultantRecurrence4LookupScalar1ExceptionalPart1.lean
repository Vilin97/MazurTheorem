/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupExceptionalProduct
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupC1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Exceptional coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence4Scalar1Exceptional_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (161 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_161_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (161 + x) *
        remainder6Coefficient1.coeff (161 - (161 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 161 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (161 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (161 - (161 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_161 :
    recurrence4Scalar1Exceptional.coeff 161 =
      -((((7438964948299108939445774825748553312527102567561266544571186154127004 * 10 ^ 70 +
        6290776117320429500986614576960335299119684427336421436304599133623256) * 10 ^ 70 +
        5050175829624821554218657270005244812686288229842975654416727458452438) * 10 ^ 70 +
        8824009763601847179115664293481285514365255725616444903087178660330334) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 162,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (161 - x)) = _
  rw [show 162 = 12 +
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
  rw [recurrence4Scalar1Exceptional_coeff_161_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_161_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (162 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_162_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (162 + x) *
        remainder6Coefficient1.coeff (162 - (162 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 162 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (162 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (162 - (162 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_162 :
    recurrence4Scalar1Exceptional.coeff 162 =
      (((((3 * 10 ^ 70 +
        1363564451929773600693806796189040700201585097823730084285682631880993) * 10 ^ 70 +
        9079482386936385240210531519127132044711056231605045543875475095414927) * 10 ^ 70 +
        5801606919564139270296248565898853933808404367387371757285571279184945) * 10 ^ 70 +
        5037402920409890879996960922840881450603505377196611008021146830405538) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 163,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (162 - x)) = _
  rw [show 163 = 13 +
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
  rw [recurrence4Scalar1Exceptional_coeff_162_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_162_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (163 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (163 + x) *
        remainder6Coefficient1.coeff (163 - (163 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 163 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (163 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (163 - (163 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_163 :
    recurrence4Scalar1Exceptional.coeff 163 =
      -(((((12 * 10 ^ 70 +
        9252648849833535158123183917211031940008273107098557643027992520005121) * 10 ^ 70 +
        4169691211833969287480673653682018300657165782456885124226126635031736) * 10 ^ 70 +
        7242869360164745077066210700762016094107525693395167792326480117955494) * 10 ^ 70 +
        9631645121857877815521348337407579246538342507108338331331067277940027) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (163 - x)) = _
  rw [show 164 = 14 +
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
  rw [recurrence4Scalar1Exceptional_coeff_163_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (164 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (164 + x) *
        remainder6Coefficient1.coeff (164 - (164 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 164 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (164 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (164 - (164 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_164 :
    recurrence4Scalar1Exceptional.coeff 164 =
      (((((52 * 10 ^ 70 +
        1068320060821841982563519113055400177282750103639817504589859548324415) * 10 ^ 70 +
        3926069556028659212909079483104559084416116282288731864271752871489195) * 10 ^ 70 +
        3206786806002757962541138793029043751700394911305559818702180133027345) * 10 ^ 70 +
        7285472322079783733071408773279812525129912408186401097169000559766569) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (164 - x)) = _
  rw [show 165 = 15 +
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
  rw [recurrence4Scalar1Exceptional_coeff_164_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (165 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (165 + x) *
        remainder6Coefficient1.coeff (165 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 165 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (165 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (165 - (165 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_165 :
    recurrence4Scalar1Exceptional.coeff 165 =
      -(((((205 * 10 ^ 70 +
        6283366366365814058231721049967591893574872905320780653617461211118894) * 10 ^ 70 +
        6083532299939260660086520205708483367071066529071103584143258128010250) * 10 ^ 70 +
        5447018558964992413140498721234423267837324634787609060911555295985366) * 10 ^ 70 +
        3671072427291044838367952317231620633330960550874933204447081707513586) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (165 - x)) = _
  rw [show 166 = 16 +
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
  rw [recurrence4Scalar1Exceptional_coeff_165_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (166 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (166 + x) *
        remainder6Coefficient1.coeff (166 - (166 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 166 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (166 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (166 - (166 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_166 :
    recurrence4Scalar1Exceptional.coeff 166 =
      (((((794 * 10 ^ 70 +
        7999983837753211047611038792919161983527026908205473466878455079709543) * 10 ^ 70 +
        4273571933292225008221942496200029240436596656151979416645274905880309) * 10 ^ 70 +
        5823896575877052799169733587947285264271132428496553447959132862008461) * 10 ^ 70 +
        2727848970115899831437990019127425876957707632071210700161557139781592) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (166 - x)) = _
  rw [show 167 = 17 +
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
  rw [recurrence4Scalar1Exceptional_coeff_166_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (167 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (167 + x) *
        remainder6Coefficient1.coeff (167 - (167 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 167 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (167 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (167 - (167 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_167 :
    recurrence4Scalar1Exceptional.coeff 167 =
      -(((((3010 * 10 ^ 70 +
        5223070554354595993495862419736152430896352775217802526770699418023718) * 10 ^ 70 +
        2510873893723705114231559355936962157899070353195639585429012845592716) * 10 ^ 70 +
        4416314559862025114092512658449162272896985557032737444074561760332439) * 10 ^ 70 +
        6160505099752697499034778105673547702502848379518634884944475697024419) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (167 - x)) = _
  rw [show 168 = 18 +
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
  rw [recurrence4Scalar1Exceptional_coeff_167_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (168 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (168 + x) *
        remainder6Coefficient1.coeff (168 - (168 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 168 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (168 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (168 - (168 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_168 :
    recurrence4Scalar1Exceptional.coeff 168 =
      (((((11179 * 10 ^ 70 +
        7476057647532745538514761008329270916988361849280202999750385067370129) * 10 ^ 70 +
        7356680891605717732660340891475278956630566130391595099256028230912722) * 10 ^ 70 +
        7316259994310957252332748685901075458868349776006953824441499869152825) * 10 ^ 70 +
        0460966893697431959896762156399640250043951398697893473480700372355285) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (168 - x)) = _
  rw [show 169 = 19 +
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
  rw [recurrence4Scalar1Exceptional_coeff_168_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (169 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (169 + x) *
        remainder6Coefficient1.coeff (169 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 169 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (169 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (169 - (169 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_169 :
    recurrence4Scalar1Exceptional.coeff 169 =
      -(((((40719 * 10 ^ 70 +
        6721515551779084350101809043150587210028956125491007142061874994408612) * 10 ^ 70 +
        8083332643594246465442965156611250833241551737014197710268298901669993) * 10 ^ 70 +
        0688127687438139855498285981782240175644971988322149717108371543070758) * 10 ^ 70 +
        2234018860980991142051995151296125858863660489321364491225530412311032) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (169 - x)) = _
  rw [show 170 = 20 +
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
  rw [recurrence4Scalar1Exceptional_coeff_169_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (170 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (170 + x) *
        remainder6Coefficient1.coeff (170 - (170 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 170 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (170 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (170 - (170 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_170 :
    recurrence4Scalar1Exceptional.coeff 170 =
      (((((145518 * 10 ^ 70 +
        0796015193231556512052104612986119262924000425099698588635286727249088) * 10 ^ 70 +
        8694091417367398136285503858708659168025303081102975336985925245091015) * 10 ^ 70 +
        2537871584236222742246978135646220624849297195524515187550792867357130) * 10 ^ 70 +
        7850630187116786525854422726810903408035547102939378224810731507332847) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (170 - x)) = _
  rw [show 171 = 21 +
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
  rw [recurrence4Scalar1Exceptional_coeff_170_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (171 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (171 + x) *
        remainder6Coefficient1.coeff (171 - (171 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 171 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (171 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (171 - (171 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_171 :
    recurrence4Scalar1Exceptional.coeff 171 =
      -(((((510403 * 10 ^ 70 +
        1687815335865052082530613394857167814450069816814049184553617808357581) * 10 ^ 70 +
        4693337749292881331402453841916286369321776512173851110590902312977802) * 10 ^ 70 +
        1193889536363344706658382352430024169195233795103925948649423183110878) * 10 ^ 70 +
        8035420806056872070070026677022994328143981779075576239720664745179974) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (171 - x)) = _
  rw [show 172 = 22 +
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
  rw [recurrence4Scalar1Exceptional_coeff_171_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (172 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (172 + x) *
        remainder6Coefficient1.coeff (172 - (172 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 172 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (172 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (172 - (172 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_172 :
    recurrence4Scalar1Exceptional.coeff 172 =
      (((((1757616 * 10 ^ 70 +
        1313326992839288674311728711638413764934476352668289637055841107643844) * 10 ^ 70 +
        6999825939171911145901304567615496908936261008705798939916191213185350) * 10 ^ 70 +
        1416965734725870765608281253601886719986269868712042616629254800093632) * 10 ^ 70 +
        5235564788281859153823733113684450852899899799150393504831783252006622) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (172 - x)) = _
  rw [show 173 = 23 +
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
  rw [recurrence4Scalar1Exceptional_coeff_172_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (173 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (173 + x) *
        remainder6Coefficient1.coeff (173 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 173 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (173 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (173 - (173 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_173 :
    recurrence4Scalar1Exceptional.coeff 173 =
      -(((((5943858 * 10 ^ 70 +
        8847804968042767810875540181922795804435788665994661264340934936141271) * 10 ^ 70 +
        0943501467835154236034780647864125043285143719411258191850951711951967) * 10 ^ 70 +
        0873429764943098233812758876345181796683247005887051402993392453150304) * 10 ^ 70 +
        1387580019352011078673823759802483899774965448323318534905005818445814) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (173 - x)) = _
  rw [show 174 = 24 +
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
  rw [recurrence4Scalar1Exceptional_coeff_173_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (174 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (174 + x) *
        remainder6Coefficient1.coeff (174 - (174 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 174 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (174 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (174 - (174 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_174 :
    recurrence4Scalar1Exceptional.coeff 174 =
      (((((19744981 * 10 ^ 70 +
        4854957278864137619656728110125926611944792546064637454041580051596234) * 10 ^ 70 +
        0309270751373891299890994052725990993101319396716970334144627335475578) * 10 ^ 70 +
        6202443257602156364291871407078707539205311092306879025116470850886516) * 10 ^ 70 +
        6137611855007491036277626017308198807578306488712425806667937596896359) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (174 - x)) = _
  rw [show 175 = 25 +
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
  rw [recurrence4Scalar1Exceptional_coeff_174_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (175 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (175 + x) *
        remainder6Coefficient1.coeff (175 - (175 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 175 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (175 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (175 - (175 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_175 :
    recurrence4Scalar1Exceptional.coeff 175 =
      -(((((64445174 * 10 ^ 70 +
        7092464820502279284357775706118787813093234482110838363656710767374581) * 10 ^ 70 +
        2035589556844066977644708788042342754946623422648473589715765710022566) * 10 ^ 70 +
        5491397041078857685705041562457576919911697043774712850275923994188037) * 10 ^ 70 +
        0724343966868803552114699657268222266082272360291574500033539595991532) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (175 - x)) = _
  rw [show 176 = 26 +
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
  rw [recurrence4Scalar1Exceptional_coeff_175_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (176 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (176 + x) *
        remainder6Coefficient1.coeff (176 - (176 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 176 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (176 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (176 - (176 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_176 :
    recurrence4Scalar1Exceptional.coeff 176 =
      (((((206711120 * 10 ^ 70 +
        9175733865413021509842234836493427785931873073513143516762777960713058) * 10 ^ 70 +
        8794891701250073875320023959691832977728530888530617863613983407793861) * 10 ^ 70 +
        8913455262298091327806153155244094958216794553632642154756027607536628) * 10 ^ 70 +
        3313101166158743143228540659331264363141028380616123470719966098437335) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (176 - x)) = _
  rw [show 177 = 27 +
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
  rw [recurrence4Scalar1Exceptional_coeff_176_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (177 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (177 + x) *
        remainder6Coefficient1.coeff (177 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 177 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (177 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (177 - (177 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_177 :
    recurrence4Scalar1Exceptional.coeff 177 =
      -(((((651725768 * 10 ^ 70 +
        3324897709904161733548219012201094447339143611527194481221632773761911) * 10 ^ 70 +
        7012546372483292489349731354104536212481394142967510564861425125406220) * 10 ^ 70 +
        1081632961768068502023538012875094192766136258835339612190748587179960) * 10 ^ 70 +
        0780204353366687063222990073014799462585046059877763208087279778099528) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (177 - x)) = _
  rw [show 178 = 28 +
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
  rw [recurrence4Scalar1Exceptional_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (178 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (178 + x) *
        remainder6Coefficient1.coeff (178 - (178 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 178 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (178 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (178 - (178 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_178 :
    recurrence4Scalar1Exceptional.coeff 178 =
      (((((2020112948 * 10 ^ 70 +
        5460157049141198767020045927583815496749545749040895780381854133558109) * 10 ^ 70 +
        5235538523917783721086312367078628583803889634973178117698489385847874) * 10 ^ 70 +
        6671544349350398533226409489309104926061864373265301400298841824055824) * 10 ^ 70 +
        2929853707871445862567522930626980807408091909362847506938214107826804) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (178 - x)) = _
  rw [show 179 = 29 +
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
  rw [recurrence4Scalar1Exceptional_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (179 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (179 + x) *
        remainder6Coefficient1.coeff (179 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 179 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (179 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (179 - (179 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_179 :
    recurrence4Scalar1Exceptional.coeff 179 =
      -(((((6157055540 * 10 ^ 70 +
        6607086122235701833654608495742161752260760226905507231795413728125114) * 10 ^ 70 +
        6285151884295080362916006509678515266706053584943003240146235484166099) * 10 ^ 70 +
        9019781956107537234221595775303946015999211294796123985365198420326464) * 10 ^ 70 +
        3920861332001046404153599253056497178829455985213161861715109622985613) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (179 - x)) = _
  rw [show 180 = 30 +
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
  rw [recurrence4Scalar1Exceptional_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (180 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (180 + x) *
        remainder6Coefficient1.coeff (180 - (180 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 180 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (180 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (180 - (180 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_180 :
    recurrence4Scalar1Exceptional.coeff 180 =
      (((((18455655722 * 10 ^ 70 +
        4045330081579088003778830876301869192246637944894645943662130048188481) * 10 ^ 70 +
        7178153703566813172078823680649786854786961987667139462195890307179095) * 10 ^ 70 +
        5676465316020677736247697578082975894144883104109498268865005996209310) * 10 ^ 70 +
        7498811251958810593232118818048610500484976493999499137447345145600041) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (180 - x)) = _
  rw [show 181 = 31 +
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
  rw [recurrence4Scalar1Exceptional_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (181 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (181 + x) *
        remainder6Coefficient1.coeff (181 - (181 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 181 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (181 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (181 - (181 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_181 :
    recurrence4Scalar1Exceptional.coeff 181 =
      -(((((54414299582 * 10 ^ 70 +
        9043926116934853322694043729609931163251728058729158256672934206424403) * 10 ^ 70 +
        1248111700669973336583941814257022056091031380295470642234977657465986) * 10 ^ 70 +
        0447066216777542602338955773350567050492202989093655550882018929601227) * 10 ^ 70 +
        1718620820145336521416231718968383610226253180196564944502147934879724) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (181 - x)) = _
  rw [show 182 = 32 +
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
  rw [recurrence4Scalar1Exceptional_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (182 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (182 + x) *
        remainder6Coefficient1.coeff (182 - (182 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 182 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (182 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (182 - (182 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_182 :
    recurrence4Scalar1Exceptional.coeff 182 =
      (((((157829489121 * 10 ^ 70 +
        1469001873579943117442770330785935826663905207265413179780070125752250) * 10 ^ 70 +
        8027985091038400519932118113730622240125729646883797080916680439845786) * 10 ^ 70 +
        3582622903789392975783481635188884581459694096624338915309854141337953) * 10 ^ 70 +
        4857736834758219211339537427819991200410132777788461702354808509716286) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (182 - x)) = _
  rw [show 183 = 33 +
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
  rw [recurrence4Scalar1Exceptional_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (183 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (183 + x) *
        remainder6Coefficient1.coeff (183 - (183 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 183 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (183 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (183 - (183 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_183 :
    recurrence4Scalar1Exceptional.coeff 183 =
      -(((((450418022346 * 10 ^ 70 +
        8082303849485945550754107761165667315715292618747083419576596986510706) * 10 ^ 70 +
        0339439772445674946519258937955373051286340806526736719115497666285216) * 10 ^ 70 +
        0052208819047618032839916223004039086199878282494256132332390564718195) * 10 ^ 70 +
        3858272122371808459426235052594919747754312498113137517813282754885483) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (183 - x)) = _
  rw [show 184 = 34 +
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
  rw [recurrence4Scalar1Exceptional_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (184 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (184 + x) *
        remainder6Coefficient1.coeff (184 - (184 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 184 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (184 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (184 - (184 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_184 :
    recurrence4Scalar1Exceptional.coeff 184 =
      (((((1264892717438 * 10 ^ 70 +
        5469675591598438564061010005035547145964281111700787327074347718225880) * 10 ^ 70 +
        4323324002961695002248148733496051957239071843483836995050952299715217) * 10 ^ 70 +
        1043072030412557359621965315931367764995552110124048003288082117073690) * 10 ^ 70 +
        6816242171706640245741079993374321803994399170088679249814439331742231) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (184 - x)) = _
  rw [show 185 = 35 +
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
  rw [recurrence4Scalar1Exceptional_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (185 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (185 + x) *
        remainder6Coefficient1.coeff (185 - (185 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 185 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (185 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (185 - (185 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_185 :
    recurrence4Scalar1Exceptional.coeff 185 =
      -(((((3495883087480 * 10 ^ 70 +
        8569555973244083285638433747282797679979705481796118625115978055199776) * 10 ^ 70 +
        5401183156178840929813459261934498266310082017015107774938196410760865) * 10 ^ 70 +
        8311726362776462310557877284691787537989775036661112338590868794806001) * 10 ^ 70 +
        9183528333971176357684994711794909148137710337509638461968682174297931) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (185 - x)) = _
  rw [show 186 = 36 +
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
  rw [recurrence4Scalar1Exceptional_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (186 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (186 + x) *
        remainder6Coefficient1.coeff (186 - (186 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 186 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (186 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (186 - (186 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_186 :
    recurrence4Scalar1Exceptional.coeff 186 =
      (((((9509938186458 * 10 ^ 70 +
        1927770385667517458701791415684749965145609027658224332761613172890782) * 10 ^ 70 +
        1529592827845433355403504416314249860673263471397831075747205637365408) * 10 ^ 70 +
        4354666120628526546394203873587426797321184623135824133864237910965262) * 10 ^ 70 +
        4952424548145844422126945640110218168177093969445868728988285342725592) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (186 - x)) = _
  rw [show 187 = 37 +
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
  rw [recurrence4Scalar1Exceptional_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (187 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (187 + x) *
        remainder6Coefficient1.coeff (187 - (187 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 187 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (187 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (187 - (187 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_187 :
    recurrence4Scalar1Exceptional.coeff 187 =
      -(((((25466305768267 * 10 ^ 70 +
        9667783562344898895868124458079572866797019681653268525070591507796145) * 10 ^ 70 +
        5400128544300889429863259580508965138485019983585077081468598393508559) * 10 ^ 70 +
        1651461294220336227479371143884318660236639752955237216086144806040148) * 10 ^ 70 +
        0021166976929955088728393550075446929217843717265779625870960885260425) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (187 - x)) = _
  rw [show 188 = 38 +
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
  rw [recurrence4Scalar1Exceptional_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (188 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (188 + x) *
        remainder6Coefficient1.coeff (188 - (188 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 188 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (188 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (188 - (188 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_188 :
    recurrence4Scalar1Exceptional.coeff 188 =
      (((((67138137230604 * 10 ^ 70 +
        5468645872041613536001757446614023961678703195935075954515888608841166) * 10 ^ 70 +
        9820797927217924383428569674549387760578008434399964455764659463113311) * 10 ^ 70 +
        2280726234785589680111000423446821016202069668227698365513813432312075) * 10 ^ 70 +
        3264069759437462225718023350827233882737070054226584032829932044798872) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (188 - x)) = _
  rw [show 189 = 39 +
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
  rw [recurrence4Scalar1Exceptional_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (189 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (189 + x) *
        remainder6Coefficient1.coeff (189 - (189 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 189 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (189 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (189 - (189 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_189 :
    recurrence4Scalar1Exceptional.coeff 189 =
      -(((((174274256779095 * 10 ^ 70 +
        4246596764701138958515543337838632269096547729353548046064994802034981) * 10 ^ 70 +
        2259377417957881297317392407197594710587262314832536083597840887880741) * 10 ^ 70 +
        8034338046479086814810695073106095328417789245058881709392194932186302) * 10 ^ 70 +
        2756822870442732711393892852280158899795467837706082893166908732030625) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (189 - x)) = _
  rw [show 190 = 40 +
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
  rw [recurrence4Scalar1Exceptional_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (190 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (190 + x) *
        remainder6Coefficient1.coeff (190 - (190 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 190 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (190 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (190 - (190 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_190 :
    recurrence4Scalar1Exceptional.coeff 190 =
      (((((445452488562642 * 10 ^ 70 +
        5183848462733386335999570134496983649701032689402720300943813556765131) * 10 ^ 70 +
        8164205680061930524923755407370561593679637003539688731298206446700531) * 10 ^ 70 +
        2224426483532633206207385171981577083914390373427742375777489648968798) * 10 ^ 70 +
        7202329494542158767191777735305041292149658018356253082033139125919820) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (190 - x)) = _
  rw [show 191 = 41 +
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
  rw [recurrence4Scalar1Exceptional_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (191 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (191 + x) *
        remainder6Coefficient1.coeff (191 - (191 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 191 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (191 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (191 - (191 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_191 :
    recurrence4Scalar1Exceptional.coeff 191 =
      -(((((1121283695312016 * 10 ^ 70 +
        2327076605124482169761132701323779388448146841153916793782680577147628) * 10 ^ 70 +
        2683991509448513955328447966656709678094151443651606358261285091077636) * 10 ^ 70 +
        7254118470735422692533544164950043539841596561068844679572948383273910) * 10 ^ 70 +
        4969248723466527482805147666902527529486244695590837288814816275433986) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (191 - x)) = _
  rw [show 192 = 42 +
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
  rw [recurrence4Scalar1Exceptional_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (192 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (192 + x) *
        remainder6Coefficient1.coeff (192 - (192 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 192 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (192 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (192 - (192 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_192 :
    recurrence4Scalar1Exceptional.coeff 192 =
      (((((2779813518424250 * 10 ^ 70 +
        7148137826801893371149906442589752204957387222577817285663184039605329) * 10 ^ 70 +
        8439566380423620106920482625768542575414641781436975942698224238499253) * 10 ^ 70 +
        2530702931025315547399892132284379199918401177221551418872771203854246) * 10 ^ 70 +
        3178898361227638393103089272610055144853019862718542048242628283665033) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (192 - x)) = _
  rw [show 193 = 43 +
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
  rw [recurrence4Scalar1Exceptional_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (193 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (193 + x) *
        remainder6Coefficient1.coeff (193 - (193 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 193 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (193 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (193 - (193 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_193 :
    recurrence4Scalar1Exceptional.coeff 193 =
      -(((((6787976560522579 * 10 ^ 70 +
        1553214965086813833066115642359194621596723354563502467411536077342588) * 10 ^ 70 +
        7267697550522336807211767024828110456245908036604466395434201805392387) * 10 ^ 70 +
        9347581922321443345826930106384788858819047024558600734767884809593049) * 10 ^ 70 +
        1539702288527895903434989918185723726531222815039640911355568998335547) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (193 - x)) = _
  rw [show 194 = 44 +
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
  rw [recurrence4Scalar1Exceptional_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (194 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (194 + x) *
        remainder6Coefficient1.coeff (194 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 194 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (194 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (194 - (194 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_194 :
    recurrence4Scalar1Exceptional.coeff 194 =
      (((((16327756023804062 * 10 ^ 70 +
        8370579136336663780738695884282135195177789972126557878496499391393202) * 10 ^ 70 +
        4225777452988758926037183998355506661771022604000511513592322397382100) * 10 ^ 70 +
        0187220403566126524645515733691461485351846523157427977211657507425253) * 10 ^ 70 +
        1295389649568266822934965461514998830303978028704855217615597227637735) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (194 - x)) = _
  rw [show 195 = 45 +
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
  rw [recurrence4Scalar1Exceptional_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (195 + x) *
        remainder6Coefficient1.coeff (195 - (195 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 195 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (195 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (195 - (195 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_195 :
    recurrence4Scalar1Exceptional.coeff 195 =
      -(((((38690980772806841 * 10 ^ 70 +
        9990698911030130224227822980462321421967646416922933526390130600936019) * 10 ^ 70 +
        9841712315638134946841336451436212747189253562393997764540491855419188) * 10 ^ 70 +
        4111791493636067065763779491023156350393028708559917132855712555095165) * 10 ^ 70 +
        1536658039902948795157961915524920107780873412841683677287068950682787) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (195 - x)) = _
  rw [show 196 = 46 +
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
  rw [recurrence4Scalar1Exceptional_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (196 + x) *
        remainder6Coefficient1.coeff (196 - (196 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 196 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (196 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (196 - (196 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_196 :
    recurrence4Scalar1Exceptional.coeff 196 =
      (((((90328392860429250 * 10 ^ 70 +
        7649808417870296064420697919681902145290123949894837022524007998409219) * 10 ^ 70 +
        5731284112073627086857834207843832505341418172129630735330259097056320) * 10 ^ 70 +
        7158487789557352713695537390743866350584389651048610057500845446664815) * 10 ^ 70 +
        3619182845639203192849045447113379052315846450542715736850484038917990) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (196 - x)) = _
  rw [show 197 = 47 +
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
  rw [recurrence4Scalar1Exceptional_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (197 + x) *
        remainder6Coefficient1.coeff (197 - (197 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 197 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (197 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (197 - (197 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_197 :
    recurrence4Scalar1Exceptional.coeff 197 =
      -(((((207779701020449656 * 10 ^ 70 +
        7017713482120872903191334382341256709972440528541472760190439776152345) * 10 ^ 70 +
        5061517972250609699582851600484220404265104191247922583543170474604959) * 10 ^ 70 +
        3081558255856669312598755998393083867380107725220412237610410341543059) * 10 ^ 70 +
        3719879993197611370415958672857339554065960803859079028161845052289870) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (197 - x)) = _
  rw [show 198 = 48 +
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
  rw [recurrence4Scalar1Exceptional_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (198 + x) *
        remainder6Coefficient1.coeff (198 - (198 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 198 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (198 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (198 - (198 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_198 :
    recurrence4Scalar1Exceptional.coeff 198 =
      (((((470953499115382570 * 10 ^ 70 +
        7728231198694697200833296064742393647764463382959230101080398110549002) * 10 ^ 70 +
        3300874817768007778478345815743028164940383068126226104363096081903791) * 10 ^ 70 +
        0828923448986297900673683360570033414545666884475258113863737546703828) * 10 ^ 70 +
        5117010405486565496808875998654370359793328002217265128640894979706074) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (198 - x)) = _
  rw [show 199 = 49 +
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
  rw [recurrence4Scalar1Exceptional_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (199 + x) *
        remainder6Coefficient1.coeff (199 - (199 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 199 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (199 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (199 - (199 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_199 :
    recurrence4Scalar1Exceptional.coeff 199 =
      -(((((1051912633987965812 * 10 ^ 70 +
        3475139372643520259786163593396137862837482694252641580684321242478904) * 10 ^ 70 +
        5284593898697652061880612957910596097664620326125393412996136737364036) * 10 ^ 70 +
        7545121453431183722048134541339726399165758620983847329002528969685931) * 10 ^ 70 +
        6414142608704039336001891940415313999640210799257494882042005687712507) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (199 - x)) = _
  rw [show 200 = 50 +
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
  rw [recurrence4Scalar1Exceptional_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (200 + x) *
        remainder6Coefficient1.coeff (200 - (200 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 200 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (200 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (200 - (200 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_200 :
    recurrence4Scalar1Exceptional.coeff 200 =
      (((((2315461819659547640 * 10 ^ 70 +
        2203993738586398359466918840703099020901224898157692856509061561862264) * 10 ^ 70 +
        6826077620836301535913624016110124737921696056632151804444587326027622) * 10 ^ 70 +
        6003459507255056656694692484348716481432929717658468948058749194495120) * 10 ^ 70 +
        7859526622310443484711408307593037080284019032547695812854848286780034) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (200 - x)) = _
  rw [show 201 = 51 +
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
  rw [recurrence4Scalar1Exceptional_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (201 + x) *
        remainder6Coefficient1.coeff (201 - (201 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 201 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (201 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (201 - (201 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_201 :
    recurrence4Scalar1Exceptional.coeff 201 =
      -(((((5023199623102878113 * 10 ^ 70 +
        5317641575023789970755595123897737856793539918001255211671152135065921) * 10 ^ 70 +
        2686379367014216145491503391401759899966112345761255325296638422648898) * 10 ^ 70 +
        7622272115602396517000043727096718673028192296040057837076212920623608) * 10 ^ 70 +
        5914365622814251147431110304393136947140245406841886966188260459970877) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (201 - x)) = _
  rw [show 202 = 52 +
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
  rw [recurrence4Scalar1Exceptional_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (202 + x) *
        remainder6Coefficient1.coeff (202 - (202 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 202 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (202 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (202 - (202 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_202 :
    recurrence4Scalar1Exceptional.coeff 202 =
      (((((10740776551994997096 * 10 ^ 70 +
        1284113598763881997519443868117628784679081933377358046827917435563127) * 10 ^ 70 +
        1832001042397767553407153303500259558569606863303237457870381351382881) * 10 ^ 70 +
        1237330839351269353301450257384875897259897925752775667353443776734271) * 10 ^ 70 +
        3094643357178269887166287564970926404359631258970059173231503954254552) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (202 - x)) = _
  rw [show 203 = 53 +
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
  rw [recurrence4Scalar1Exceptional_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (203 + x) *
        remainder6Coefficient1.coeff (203 - (203 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 203 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (203 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (203 - (203 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_203 :
    recurrence4Scalar1Exceptional.coeff 203 =
      -(((((22637579622777536778 * 10 ^ 70 +
        8152791752679591116467220867574985342241299548741985493021637612802462) * 10 ^ 70 +
        9714697333435905576930018484420376631760544358166728449682305754117944) * 10 ^ 70 +
        5220189406462048072810240818372000533157846246895019280728568720601409) * 10 ^ 70 +
        8803668187418924788271963245919281000225370596304453877002590595261297) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (203 - x)) = _
  rw [show 204 = 54 +
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
  rw [recurrence4Scalar1Exceptional_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (204 + x) *
        remainder6Coefficient1.coeff (204 - (204 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 204 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (204 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (204 - (204 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_204 :
    recurrence4Scalar1Exceptional.coeff 204 =
      (((((47031529419747877083 * 10 ^ 70 +
        0978497111602233218521161115404719492326961374706693844566913154049341) * 10 ^ 70 +
        7604930184355855905136465036252403419881295861525877603913148096555960) * 10 ^ 70 +
        4651787651942990937332404335420097007312947240558517134477976045819684) * 10 ^ 70 +
        8672509946767454535633176234223263026691764376781853831220444725599582) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (204 - x)) = _
  rw [show 205 = 55 +
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
  rw [recurrence4Scalar1Exceptional_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (227 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (227 + x) *
        remainder6Coefficient1.coeff (227 - (227 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 227 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (227 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (227 - (227 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_227 :
    recurrence4Scalar1Exceptional.coeff 227 =
      -(((((20113129604923859616082162 * 10 ^ 70 +
        1059559928638866628028808745728605223647614398552862111524706754591923) * 10 ^ 70 +
        2608645026559552089412704711954101387548601382067115109475218384367170) * 10 ^ 70 +
        0324318459952250692931367784555374133025433933182392704242029908545140) * 10 ^ 70 +
        0410757151492105633318028892342457637446674985743107222633455332243461) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (227 - x)) = _
  rw [show 228 = 78 +
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
  rw [recurrence4Scalar1Exceptional_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (228 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (228 + x) *
        remainder6Coefficient1.coeff (228 - (228 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 228 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (228 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (228 - (228 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_228 :
    recurrence4Scalar1Exceptional.coeff 228 =
      (((((30010228207890684904497319 * 10 ^ 70 +
        0971704108101876921153901153603274197366953816587148722430993945987888) * 10 ^ 70 +
        5337841467184703807178654567828102361858306400462261154825436244352176) * 10 ^ 70 +
        2664295452469426143420914820973234732859908883492819082118450249102142) * 10 ^ 70 +
        9108777548350841066326468384952638627889643627148211252467164359566838) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (228 - x)) = _
  rw [show 229 = 79 +
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
  rw [recurrence4Scalar1Exceptional_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (229 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (229 + x) *
        remainder6Coefficient1.coeff (229 - (229 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 229 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (229 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (229 - (229 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_229 :
    recurrence4Scalar1Exceptional.coeff 229 =
      -(((((44182535169958162041597275 * 10 ^ 70 +
        9990669025178031951396718332645286743653823294686156172597423206754136) * 10 ^ 70 +
        3024851022758383808562157057244103170874697062877522558324447664841034) * 10 ^ 70 +
        4865906692244456634325746000122762764286629131383491037543984563232601) * 10 ^ 70 +
        4557685494556135041655897679077477743290267877158117731078668824743708) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (229 - x)) = _
  rw [show 230 = 80 +
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
  rw [recurrence4Scalar1Exceptional_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (230 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (230 + x) *
        remainder6Coefficient1.coeff (230 - (230 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 230 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (230 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (230 - (230 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_230 :
    recurrence4Scalar1Exceptional.coeff 230 =
      (((((64185067443980708468968048 * 10 ^ 70 +
        6388852475465604442549216829411985482998936415259277555954264360849987) * 10 ^ 70 +
        5425475009978490729098273872600699725900081743827080145009926045034796) * 10 ^ 70 +
        7012972620542400251723942264150199222946071948240065663639139092490853) * 10 ^ 70 +
        4429019226170963550983447866373517833023520412862886677623028269122369) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (230 - x)) = _
  rw [show 231 = 81 +
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
  rw [recurrence4Scalar1Exceptional_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (231 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (231 + x) *
        remainder6Coefficient1.coeff (231 - (231 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 231 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (231 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (231 - (231 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_231 :
    recurrence4Scalar1Exceptional.coeff 231 =
      -(((((92008793119435030555953685 * 10 ^ 70 +
        0400276567311326070332099989342146672636967180847799227867204916978488) * 10 ^ 70 +
        9078410367144770253043555494843548179155062465639367312575031220175868) * 10 ^ 70 +
        4058672059066966810666864167477141977857512428396586134415495814039207) * 10 ^ 70 +
        9876297529446049415436405675623575249938975389339731817955197213760558) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (231 - x)) = _
  rw [show 232 = 82 +
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
  rw [recurrence4Scalar1Exceptional_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (232 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (232 + x) *
        remainder6Coefficient1.coeff (232 - (232 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 232 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (232 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (232 - (232 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_232 :
    recurrence4Scalar1Exceptional.coeff 232 =
      (((((130150589264685370838016906 * 10 ^ 70 +
        2347771188489369916924388213840386765209591153026481229200748652512993) * 10 ^ 70 +
        2876485863814814950652948853347283742111508206258068057854782943607212) * 10 ^ 70 +
        9792212371966331208226712225190603295639528604122267644544963617605476) * 10 ^ 70 +
        1127585503454870074997852606711162633091597153976910115328260724019964) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (232 - x)) = _
  rw [show 233 = 83 +
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
  rw [recurrence4Scalar1Exceptional_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (233 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (233 + x) *
        remainder6Coefficient1.coeff (233 - (233 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 233 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (233 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (233 - (233 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_233 :
    recurrence4Scalar1Exceptional.coeff 233 =
      -(((((181674308763356706509862102 * 10 ^ 70 +
        5215800502835789279007027394313522797127601217350067935554335418220461) * 10 ^ 70 +
        2808837472506184944134229956891696253577398204187658545551994408688463) * 10 ^ 70 +
        2159089819506995188076323766166953916404694064757694753429328378165737) * 10 ^ 70 +
        3331105764900740833042584397264624021805579486056004484491248022505337) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (233 - x)) = _
  rw [show 234 = 84 +
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
  rw [recurrence4Scalar1Exceptional_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (234 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (234 + x) *
        remainder6Coefficient1.coeff (234 - (234 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 234 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (234 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (234 - (234 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_234 :
    recurrence4Scalar1Exceptional.coeff 234 =
      (((((250253502075239949029919844 * 10 ^ 70 +
        6831522812058553965509843687915972136653002077369120188159071446474735) * 10 ^ 70 +
        3741990981936827333674989236453318317146549429586958896492572487137338) * 10 ^ 70 +
        8401961758657962766269025067861219148865000729110916250456505891009618) * 10 ^ 70 +
        0258247576241425130089591331953818978387762479940797778347592364055517) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (234 - x)) = _
  rw [show 235 = 85 +
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
  rw [recurrence4Scalar1Exceptional_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (235 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (235 + x) *
        remainder6Coefficient1.coeff (235 - (235 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 235 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (235 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (235 - (235 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_235 :
    recurrence4Scalar1Exceptional.coeff 235 =
      -(((((340184387540537337159660319 * 10 ^ 70 +
        0927887006113514064856211129962028847960788681021311734740611682800135) * 10 ^ 70 +
        8219580103954136047874339512003756725038003769630269123222970955493141) * 10 ^ 70 +
        9803964342079078347665164077158726750493581405724096126349126804582222) * 10 ^ 70 +
        6798987620906414113626485232263902696587842228829744361212273925865616) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (235 - x)) = _
  rw [show 236 = 86 +
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
  rw [recurrence4Scalar1Exceptional_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (236 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (236 + x) *
        remainder6Coefficient1.coeff (236 - (236 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 236 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (236 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (236 - (236 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_236 :
    recurrence4Scalar1Exceptional.coeff 236 =
      (((((456356313198773431075153311 * 10 ^ 70 +
        8651024667492798131006317982121818245112296256811694776892447828043120) * 10 ^ 70 +
        0798244305257769202729780758826569031134295715368810600774633629270617) * 10 ^ 70 +
        5380287475653792429201085845289878556843212747365348355440807163282736) * 10 ^ 70 +
        7600625322255893771779399238292835801428658176122182675882085944329071) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (236 - x)) = _
  rw [show 237 = 87 +
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
  rw [recurrence4Scalar1Exceptional_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (237 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (237 + x) *
        remainder6Coefficient1.coeff (237 - (237 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 237 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (237 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (237 - (237 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_237 :
    recurrence4Scalar1Exceptional.coeff 237 =
      -(((((604166625575891624506492001 * 10 ^ 70 +
        8073113952744384764508085815493061346530176079505667284792728129126064) * 10 ^ 70 +
        1169283894090093982115305714670068695719822092632542574524060166375367) * 10 ^ 70 +
        1270538129372920405634523933186741572054845455912276381766331249594277) * 10 ^ 70 +
        4828498556070633345264814024507012353969798128592765856493767662199102) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (237 - x)) = _
  rw [show 238 = 88 +
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
  rw [recurrence4Scalar1Exceptional_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (238 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (238 + x) *
        remainder6Coefficient1.coeff (238 - (238 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 238 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (238 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (238 - (238 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_238 :
    recurrence4Scalar1Exceptional.coeff 238 =
      (((((789367986073853247108649486 * 10 ^ 70 +
        4540711392261212105427957439096079986241571817208552902994876240129445) * 10 ^ 70 +
        7134393445511049262922753947070962908818889278381870946850443601126659) * 10 ^ 70 +
        2950565534353320077155601639422674027902494356318187489558700702277273) * 10 ^ 70 +
        0790816517549171333658949432344523102719881062302114348153685625877876) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (238 - x)) = _
  rw [show 239 = 89 +
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
  rw [recurrence4Scalar1Exceptional_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (239 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (239 + x) *
        remainder6Coefficient1.coeff (239 - (239 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 239 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (239 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (239 - (239 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_239 :
    recurrence4Scalar1Exceptional.coeff 239 =
      -(((((1017839123600729824371128414 * 10 ^ 70 +
        3435302420857748039179585087309924689162852222962298426616062346881852) * 10 ^ 70 +
        9623218582018989317261084299724251454641564952821716186052530374870847) * 10 ^ 70 +
        5713983787909478680869523381551031252089297425175034286658049497387288) * 10 ^ 70 +
        4214852294633342108118773985721499443755387153061494112927215364615452) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (239 - x)) = _
  rw [show 240 = 90 +
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
  rw [recurrence4Scalar1Exceptional_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (240 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (240 + x) *
        remainder6Coefficient1.coeff (240 - (240 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 240 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (240 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (240 - (240 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_240 :
    recurrence4Scalar1Exceptional.coeff 240 =
      (((((1295275011999642255891752179 * 10 ^ 70 +
        0057403587441097965486377648070550557380768028068680521254119889059619) * 10 ^ 70 +
        9011839728694004421395267833243621953156987239601660390775036486420289) * 10 ^ 70 +
        8259379339138789875124185703010343319423894116782096745658737249121445) * 10 ^ 70 +
        3706353316607752299035009177538292006862678742079183893150851409107644) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (240 - x)) = _
  rw [show 241 = 91 +
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
  rw [recurrence4Scalar1Exceptional_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (241 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (241 + x) *
        remainder6Coefficient1.coeff (241 - (241 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 241 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (241 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (241 - (241 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_241 :
    recurrence4Scalar1Exceptional.coeff 241 =
      -(((((1626799515758911966616760178 * 10 ^ 70 +
        1914322699264943747951353379264744279032114946201106953913789436142372) * 10 ^ 70 +
        1273023641153929994252652288878784674377754720640709784845025815203807) * 10 ^ 70 +
        1337861128373353125733105417294079047392222117909919968806986037932063) * 10 ^ 70 +
        5009973010919867651229187060123712005685461980875532284225275787709510) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (241 - x)) = _
  rw [show 242 = 92 +
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
  rw [recurrence4Scalar1Exceptional_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (242 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (242 + x) *
        remainder6Coefficient1.coeff (242 - (242 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 242 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (242 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (242 - (242 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_242 :
    recurrence4Scalar1Exceptional.coeff 242 =
      (((((2016512361143016423461863560 * 10 ^ 70 +
        9600732090062930053698334526244687129476016166451953855792600845459348) * 10 ^ 70 +
        2199636887683825032903414097101683230650852945934647321173274263387859) * 10 ^ 70 +
        8752864725045546395145647433964545952123691618188145048862679763124083) * 10 ^ 70 +
        3218460272631234396719749591055575754738106521161446820002176054710480) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (242 - x)) = _
  rw [show 243 = 93 +
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
  rw [recurrence4Scalar1Exceptional_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (243 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (243 + x) *
        remainder6Coefficient1.coeff (243 - (243 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 243 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (243 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (243 - (243 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_243 :
    recurrence4Scalar1Exceptional.coeff 243 =
      -(((((2466992222499810843381571013 * 10 ^ 70 +
        7897504567242274226644744940278924963396405394553288333445341317184531) * 10 ^ 70 +
        1235477750145334942213848453071658779322463958680597246425997358524144) * 10 ^ 70 +
        0312236973557035858540664731900368471304532601946007617868900647274785) * 10 ^ 70 +
        6921376433894038041205043415297249844856675365528980243935573472372675) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (243 - x)) = _
  rw [show 244 = 94 +
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
  rw [recurrence4Scalar1Exceptional_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (244 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (244 + x) *
        remainder6Coefficient1.coeff (244 - (244 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 244 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (244 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (244 - (244 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_244 :
    recurrence4Scalar1Exceptional.coeff 244 =
      (((((2978787784002340697842252208 * 10 ^ 70 +
        1025043847373812125119007698873735622811441001240380412487699893738211) * 10 ^ 70 +
        8281138276828062118974060097951835350394061073942925002368614739920019) * 10 ^ 70 +
        4228074474245792306787883276091466611772832172271963836410909995670456) * 10 ^ 70 +
        5096684915702741985392966668265400335300956986764749251461751187229760) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (244 - x)) = _
  rw [show 245 = 95 +
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
  rw [recurrence4Scalar1Exceptional_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (245 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (245 + x) *
        remainder6Coefficient1.coeff (245 - (245 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 245 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (245 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (245 - (245 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_245 :
    recurrence4Scalar1Exceptional.coeff 245 =
      -(((((3549937584571132147536733503 * 10 ^ 70 +
        3533138234245136623123330478083479514177173561237470264405270781123087) * 10 ^ 70 +
        9883623039430151590001100777900736034094096759954237613545205150438302) * 10 ^ 70 +
        7441300513145294211338139432830266391619758596548762794171369919778250) * 10 ^ 70 +
        8932213076867297271971307985414559761309459143909915980900916000344535) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (245 - x)) = _
  rw [show 246 = 96 +
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
  rw [recurrence4Scalar1Exceptional_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (246 + x) *
        remainder6Coefficient1.coeff (246 - (246 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 246 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (246 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (246 - (246 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_246 :
    recurrence4Scalar1Exceptional.coeff 246 =
      (((((4175565862880841497842741241 * 10 ^ 70 +
        4919703890504057373414122508809737238186763275695281710814089992169626) * 10 ^ 70 +
        2546523892577191016626083687492367457773749853231894160187798488030407) * 10 ^ 70 +
        3915506373948150234079557791399413171680560860091968824449088618578982) * 10 ^ 70 +
        3020309914033564568342829493260570554567332190428211581543884258582622) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (246 - x)) = _
  rw [show 247 = 97 +
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
  rw [recurrence4Scalar1Exceptional_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (247 + x) *
        remainder6Coefficient1.coeff (247 - (247 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 247 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (247 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (247 - (247 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_247 :
    recurrence4Scalar1Exceptional.coeff 247 =
      -(((((4847604103099919333189009211 * 10 ^ 70 +
        0701092228023550552059914216517848859486182800905592765941249320622849) * 10 ^ 70 +
        2623186973801409745988306708182419297553932018037872415453877099056485) * 10 ^ 70 +
        0672311099965033397701445290331052410169531347244761977124012872162889) * 10 ^ 70 +
        8326060445087970794503531940738344268817573156886370041549202290665276) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (247 - x)) = _
  rw [show 248 = 98 +
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
  rw [recurrence4Scalar1Exceptional_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (248 + x) *
        remainder6Coefficient1.coeff (248 - (248 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 248 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (248 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (248 - (248 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_248 :
    recurrence4Scalar1Exceptional.coeff 248 =
      (((((5554685401728554752174828449 * 10 ^ 70 +
        0233425830976581760512886234379546816529083565590345374224224724312316) * 10 ^ 70 +
        1080552396361191416644056047524067535229416289630300474158195572316209) * 10 ^ 70 +
        4377126571681093330729609571179451949523688471221935958819966001241030) * 10 ^ 70 +
        9205842645919839599519181449396644285006931382190914503392952064371369) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (248 - x)) = _
  rw [show 249 = 99 +
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
  rw [recurrence4Scalar1Exceptional_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Exceptional_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4C1_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Exceptional_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4ExceptionalProduct.coeff (249 + x) *
        remainder6Coefficient1.coeff (249 - (249 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 369 < 249 + x
  · rw [recurrence4ExceptionalProduct_coeff_high (249 + x) hleft]
    norm_num
  · rw [recurrence4C1_coeff_low
      (249 - (249 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Exceptional_coeff_249 :
    recurrence4Scalar1Exceptional.coeff 249 =
      -(((((6282250467785144575310921659 * 10 ^ 70 +
        5820995282580334005728409979640663838971331375717967706659768759273842) * 10 ^ 70 +
        4131713901009917680972051192166102727403051320074557792207079385228820) * 10 ^ 70 +
        9484499211868859687704164015566897784655277200939463688504215377734352) * 10 ^ 70 +
        3461304633849520687925808160617154610322296444952542866440708142138720) : ℚ) := by
  unfold recurrence4Scalar1Exceptional
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    recurrence4ExceptionalProduct.coeff x * remainder6Coefficient1.coeff (249 - x)) = _
  rw [show 250 = 100 +
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
  rw [recurrence4Scalar1Exceptional_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Exceptional_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
