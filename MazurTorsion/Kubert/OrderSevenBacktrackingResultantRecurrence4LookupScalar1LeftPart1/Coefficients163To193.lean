/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar1LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A1_coeff_1
  recurrence4A1_coeff_10
  recurrence4A1_coeff_100
  recurrence4A1_coeff_101
  recurrence4A1_coeff_102
  recurrence4A1_coeff_103
  recurrence4A1_coeff_104
  recurrence4A1_coeff_105
  recurrence4A1_coeff_106
  recurrence4A1_coeff_107
  recurrence4A1_coeff_108
  recurrence4A1_coeff_109
  recurrence4A1_coeff_11
  recurrence4A1_coeff_110
  recurrence4A1_coeff_111
  recurrence4A1_coeff_112
  recurrence4A1_coeff_113
  recurrence4A1_coeff_114
  recurrence4A1_coeff_115
  recurrence4A1_coeff_116
  recurrence4A1_coeff_117
  recurrence4A1_coeff_118
  recurrence4A1_coeff_119
  recurrence4A1_coeff_12
  recurrence4A1_coeff_120
  recurrence4A1_coeff_121
  recurrence4A1_coeff_122
  recurrence4A1_coeff_123
  recurrence4A1_coeff_124
  recurrence4A1_coeff_125
  recurrence4A1_coeff_126
  recurrence4A1_coeff_127
  recurrence4A1_coeff_128
  recurrence4A1_coeff_129
  recurrence4A1_coeff_13
  recurrence4A1_coeff_130
  recurrence4A1_coeff_131
  recurrence4A1_coeff_132
  recurrence4A1_coeff_133
  recurrence4A1_coeff_134
  recurrence4A1_coeff_135
  recurrence4A1_coeff_136
  recurrence4A1_coeff_137
  recurrence4A1_coeff_138
  recurrence4A1_coeff_139
  recurrence4A1_coeff_14
  recurrence4A1_coeff_140
  recurrence4A1_coeff_141
  recurrence4A1_coeff_142
  recurrence4A1_coeff_143
  recurrence4A1_coeff_144
  recurrence4A1_coeff_145
  recurrence4A1_coeff_146
  recurrence4A1_coeff_147
  recurrence4A1_coeff_148
  recurrence4A1_coeff_149
  recurrence4A1_coeff_15
  recurrence4A1_coeff_150
  recurrence4A1_coeff_151
  recurrence4A1_coeff_152
  recurrence4A1_coeff_153
  recurrence4A1_coeff_154
  recurrence4A1_coeff_155
  recurrence4A1_coeff_156

attribute [local simp]
  recurrence4A1_coeff_157
  recurrence4A1_coeff_158
  recurrence4A1_coeff_159
  recurrence4A1_coeff_16
  recurrence4A1_coeff_160
  recurrence4A1_coeff_161
  recurrence4A1_coeff_162
  recurrence4A1_coeff_163
  recurrence4A1_coeff_164
  recurrence4A1_coeff_165
  recurrence4A1_coeff_166
  recurrence4A1_coeff_167
  recurrence4A1_coeff_168
  recurrence4A1_coeff_169
  recurrence4A1_coeff_17
  recurrence4A1_coeff_170
  recurrence4A1_coeff_171
  recurrence4A1_coeff_172
  recurrence4A1_coeff_173
  recurrence4A1_coeff_174
  recurrence4A1_coeff_175
  recurrence4A1_coeff_176
  recurrence4A1_coeff_177
  recurrence4A1_coeff_178
  recurrence4A1_coeff_179
  recurrence4A1_coeff_18
  recurrence4A1_coeff_180
  recurrence4A1_coeff_181
  recurrence4A1_coeff_182
  recurrence4A1_coeff_183
  recurrence4A1_coeff_184
  recurrence4A1_coeff_185
  recurrence4A1_coeff_186
  recurrence4A1_coeff_187
  recurrence4A1_coeff_188
  recurrence4A1_coeff_189
  recurrence4A1_coeff_19
  recurrence4A1_coeff_190
  recurrence4A1_coeff_2
  recurrence4A1_coeff_20
  recurrence4A1_coeff_21
  recurrence4A1_coeff_22
  recurrence4A1_coeff_23
  recurrence4A1_coeff_24
  recurrence4A1_coeff_25
  recurrence4A1_coeff_26
  recurrence4A1_coeff_27
  recurrence4A1_coeff_28
  recurrence4A1_coeff_29
  recurrence4A1_coeff_3
  recurrence4A1_coeff_30
  recurrence4A1_coeff_31
  recurrence4A1_coeff_32
  recurrence4A1_coeff_33
  recurrence4A1_coeff_34
  recurrence4A1_coeff_35
  recurrence4A1_coeff_36
  recurrence4A1_coeff_37
  recurrence4A1_coeff_38
  recurrence4A1_coeff_39
  recurrence4A1_coeff_4
  recurrence4A1_coeff_40
  recurrence4A1_coeff_41
  recurrence4A1_coeff_42

attribute [local simp]
  recurrence4A1_coeff_43
  recurrence4A1_coeff_44
  recurrence4A1_coeff_45
  recurrence4A1_coeff_46
  recurrence4A1_coeff_47
  recurrence4A1_coeff_48
  recurrence4A1_coeff_49
  recurrence4A1_coeff_5
  recurrence4A1_coeff_50
  recurrence4A1_coeff_51
  recurrence4A1_coeff_52
  recurrence4A1_coeff_53
  recurrence4A1_coeff_54
  recurrence4A1_coeff_55
  recurrence4A1_coeff_56
  recurrence4A1_coeff_57
  recurrence4A1_coeff_58
  recurrence4A1_coeff_59
  recurrence4A1_coeff_6
  recurrence4A1_coeff_60
  recurrence4A1_coeff_61
  recurrence4A1_coeff_62
  recurrence4A1_coeff_63
  recurrence4A1_coeff_64
  recurrence4A1_coeff_65
  recurrence4A1_coeff_66
  recurrence4A1_coeff_67
  recurrence4A1_coeff_68
  recurrence4A1_coeff_69
  recurrence4A1_coeff_7
  recurrence4A1_coeff_70
  recurrence4A1_coeff_71
  recurrence4A1_coeff_72
  recurrence4A1_coeff_73
  recurrence4A1_coeff_74
  recurrence4A1_coeff_75
  recurrence4A1_coeff_76
  recurrence4A1_coeff_77
  recurrence4A1_coeff_78
  recurrence4A1_coeff_79
  recurrence4A1_coeff_8
  recurrence4A1_coeff_80
  recurrence4A1_coeff_81
  recurrence4A1_coeff_82
  recurrence4A1_coeff_83
  recurrence4A1_coeff_84
  recurrence4A1_coeff_85
  recurrence4A1_coeff_86
  recurrence4A1_coeff_87
  recurrence4A1_coeff_88
  recurrence4A1_coeff_89
  recurrence4A1_coeff_9
  recurrence4A1_coeff_90
  recurrence4A1_coeff_91
  recurrence4A1_coeff_92
  recurrence4A1_coeff_93
  recurrence4A1_coeff_94
  recurrence4A1_coeff_95
  recurrence4A1_coeff_96
  recurrence4A1_coeff_97
  recurrence4A1_coeff_98
  recurrence4A1_coeff_99
  recurrence4LeadingSquare_coeff_0
  recurrence4LeadingSquare_coeff_1

attribute [local simp]
  recurrence4LeadingSquare_coeff_10
  recurrence4LeadingSquare_coeff_100
  recurrence4LeadingSquare_coeff_101
  recurrence4LeadingSquare_coeff_102
  recurrence4LeadingSquare_coeff_103
  recurrence4LeadingSquare_coeff_104
  recurrence4LeadingSquare_coeff_105
  recurrence4LeadingSquare_coeff_106
  recurrence4LeadingSquare_coeff_107
  recurrence4LeadingSquare_coeff_108
  recurrence4LeadingSquare_coeff_109
  recurrence4LeadingSquare_coeff_11
  recurrence4LeadingSquare_coeff_110
  recurrence4LeadingSquare_coeff_111
  recurrence4LeadingSquare_coeff_112
  recurrence4LeadingSquare_coeff_113
  recurrence4LeadingSquare_coeff_114
  recurrence4LeadingSquare_coeff_115
  recurrence4LeadingSquare_coeff_116
  recurrence4LeadingSquare_coeff_117
  recurrence4LeadingSquare_coeff_118
  recurrence4LeadingSquare_coeff_119
  recurrence4LeadingSquare_coeff_12
  recurrence4LeadingSquare_coeff_120
  recurrence4LeadingSquare_coeff_121
  recurrence4LeadingSquare_coeff_122
  recurrence4LeadingSquare_coeff_123
  recurrence4LeadingSquare_coeff_124
  recurrence4LeadingSquare_coeff_125
  recurrence4LeadingSquare_coeff_126
  recurrence4LeadingSquare_coeff_127
  recurrence4LeadingSquare_coeff_128
  recurrence4LeadingSquare_coeff_129
  recurrence4LeadingSquare_coeff_13
  recurrence4LeadingSquare_coeff_130
  recurrence4LeadingSquare_coeff_131
  recurrence4LeadingSquare_coeff_132
  recurrence4LeadingSquare_coeff_133
  recurrence4LeadingSquare_coeff_134
  recurrence4LeadingSquare_coeff_135
  recurrence4LeadingSquare_coeff_136
  recurrence4LeadingSquare_coeff_137
  recurrence4LeadingSquare_coeff_138
  recurrence4LeadingSquare_coeff_139
  recurrence4LeadingSquare_coeff_14
  recurrence4LeadingSquare_coeff_140
  recurrence4LeadingSquare_coeff_141
  recurrence4LeadingSquare_coeff_142
  recurrence4LeadingSquare_coeff_143
  recurrence4LeadingSquare_coeff_144
  recurrence4LeadingSquare_coeff_145
  recurrence4LeadingSquare_coeff_146
  recurrence4LeadingSquare_coeff_147
  recurrence4LeadingSquare_coeff_148
  recurrence4LeadingSquare_coeff_149
  recurrence4LeadingSquare_coeff_15
  recurrence4LeadingSquare_coeff_150
  recurrence4LeadingSquare_coeff_151
  recurrence4LeadingSquare_coeff_152
  recurrence4LeadingSquare_coeff_153
  recurrence4LeadingSquare_coeff_154
  recurrence4LeadingSquare_coeff_155
  recurrence4LeadingSquare_coeff_156
  recurrence4LeadingSquare_coeff_157

attribute [local simp]
  recurrence4LeadingSquare_coeff_158
  recurrence4LeadingSquare_coeff_159
  recurrence4LeadingSquare_coeff_16
  recurrence4LeadingSquare_coeff_160
  recurrence4LeadingSquare_coeff_161
  recurrence4LeadingSquare_coeff_162
  recurrence4LeadingSquare_coeff_163
  recurrence4LeadingSquare_coeff_164
  recurrence4LeadingSquare_coeff_165
  recurrence4LeadingSquare_coeff_166
  recurrence4LeadingSquare_coeff_167
  recurrence4LeadingSquare_coeff_168
  recurrence4LeadingSquare_coeff_169
  recurrence4LeadingSquare_coeff_17
  recurrence4LeadingSquare_coeff_170
  recurrence4LeadingSquare_coeff_171
  recurrence4LeadingSquare_coeff_172
  recurrence4LeadingSquare_coeff_173
  recurrence4LeadingSquare_coeff_174
  recurrence4LeadingSquare_coeff_175
  recurrence4LeadingSquare_coeff_176
  recurrence4LeadingSquare_coeff_177
  recurrence4LeadingSquare_coeff_178
  recurrence4LeadingSquare_coeff_179
  recurrence4LeadingSquare_coeff_18
  recurrence4LeadingSquare_coeff_180
  recurrence4LeadingSquare_coeff_181
  recurrence4LeadingSquare_coeff_182
  recurrence4LeadingSquare_coeff_183
  recurrence4LeadingSquare_coeff_184
  recurrence4LeadingSquare_coeff_185
  recurrence4LeadingSquare_coeff_186
  recurrence4LeadingSquare_coeff_187
  recurrence4LeadingSquare_coeff_188
  recurrence4LeadingSquare_coeff_189
  recurrence4LeadingSquare_coeff_19
  recurrence4LeadingSquare_coeff_190
  recurrence4LeadingSquare_coeff_191
  recurrence4LeadingSquare_coeff_192
  recurrence4LeadingSquare_coeff_193
  recurrence4LeadingSquare_coeff_194
  recurrence4LeadingSquare_coeff_195
  recurrence4LeadingSquare_coeff_196
  recurrence4LeadingSquare_coeff_197
  recurrence4LeadingSquare_coeff_198
  recurrence4LeadingSquare_coeff_199
  recurrence4LeadingSquare_coeff_2
  recurrence4LeadingSquare_coeff_20
  recurrence4LeadingSquare_coeff_200
  recurrence4LeadingSquare_coeff_201
  recurrence4LeadingSquare_coeff_202
  recurrence4LeadingSquare_coeff_203
  recurrence4LeadingSquare_coeff_204
  recurrence4LeadingSquare_coeff_205
  recurrence4LeadingSquare_coeff_206
  recurrence4LeadingSquare_coeff_207
  recurrence4LeadingSquare_coeff_208
  recurrence4LeadingSquare_coeff_209
  recurrence4LeadingSquare_coeff_21
  recurrence4LeadingSquare_coeff_210
  recurrence4LeadingSquare_coeff_211
  recurrence4LeadingSquare_coeff_212
  recurrence4LeadingSquare_coeff_213
  recurrence4LeadingSquare_coeff_214

attribute [local simp]
  recurrence4LeadingSquare_coeff_215
  recurrence4LeadingSquare_coeff_216
  recurrence4LeadingSquare_coeff_217
  recurrence4LeadingSquare_coeff_218
  recurrence4LeadingSquare_coeff_219
  recurrence4LeadingSquare_coeff_22
  recurrence4LeadingSquare_coeff_220
  recurrence4LeadingSquare_coeff_221
  recurrence4LeadingSquare_coeff_222
  recurrence4LeadingSquare_coeff_223
  recurrence4LeadingSquare_coeff_224
  recurrence4LeadingSquare_coeff_225
  recurrence4LeadingSquare_coeff_226
  recurrence4LeadingSquare_coeff_227
  recurrence4LeadingSquare_coeff_228
  recurrence4LeadingSquare_coeff_229
  recurrence4LeadingSquare_coeff_23
  recurrence4LeadingSquare_coeff_230
  recurrence4LeadingSquare_coeff_231
  recurrence4LeadingSquare_coeff_232
  recurrence4LeadingSquare_coeff_233
  recurrence4LeadingSquare_coeff_234
  recurrence4LeadingSquare_coeff_235
  recurrence4LeadingSquare_coeff_236
  recurrence4LeadingSquare_coeff_237
  recurrence4LeadingSquare_coeff_238
  recurrence4LeadingSquare_coeff_239
  recurrence4LeadingSquare_coeff_24
  recurrence4LeadingSquare_coeff_240
  recurrence4LeadingSquare_coeff_241
  recurrence4LeadingSquare_coeff_242
  recurrence4LeadingSquare_coeff_243
  recurrence4LeadingSquare_coeff_244
  recurrence4LeadingSquare_coeff_245
  recurrence4LeadingSquare_coeff_246
  recurrence4LeadingSquare_coeff_247
  recurrence4LeadingSquare_coeff_248
  recurrence4LeadingSquare_coeff_249
  recurrence4LeadingSquare_coeff_25
  recurrence4LeadingSquare_coeff_250
  recurrence4LeadingSquare_coeff_251
  recurrence4LeadingSquare_coeff_252
  recurrence4LeadingSquare_coeff_253
  recurrence4LeadingSquare_coeff_254
  recurrence4LeadingSquare_coeff_255
  recurrence4LeadingSquare_coeff_256
  recurrence4LeadingSquare_coeff_257
  recurrence4LeadingSquare_coeff_258
  recurrence4LeadingSquare_coeff_259
  recurrence4LeadingSquare_coeff_26
  recurrence4LeadingSquare_coeff_260
  recurrence4LeadingSquare_coeff_261
  recurrence4LeadingSquare_coeff_262
  recurrence4LeadingSquare_coeff_263
  recurrence4LeadingSquare_coeff_264
  recurrence4LeadingSquare_coeff_265
  recurrence4LeadingSquare_coeff_266
  recurrence4LeadingSquare_coeff_267
  recurrence4LeadingSquare_coeff_268
  recurrence4LeadingSquare_coeff_269
  recurrence4LeadingSquare_coeff_27
  recurrence4LeadingSquare_coeff_270
  recurrence4LeadingSquare_coeff_28
  recurrence4LeadingSquare_coeff_29

attribute [local simp]
  recurrence4LeadingSquare_coeff_3
  recurrence4LeadingSquare_coeff_30
  recurrence4LeadingSquare_coeff_31
  recurrence4LeadingSquare_coeff_32
  recurrence4LeadingSquare_coeff_33
  recurrence4LeadingSquare_coeff_34
  recurrence4LeadingSquare_coeff_35
  recurrence4LeadingSquare_coeff_36
  recurrence4LeadingSquare_coeff_37
  recurrence4LeadingSquare_coeff_38
  recurrence4LeadingSquare_coeff_39
  recurrence4LeadingSquare_coeff_4
  recurrence4LeadingSquare_coeff_40
  recurrence4LeadingSquare_coeff_41
  recurrence4LeadingSquare_coeff_42
  recurrence4LeadingSquare_coeff_43
  recurrence4LeadingSquare_coeff_44
  recurrence4LeadingSquare_coeff_45
  recurrence4LeadingSquare_coeff_46
  recurrence4LeadingSquare_coeff_47
  recurrence4LeadingSquare_coeff_48
  recurrence4LeadingSquare_coeff_49
  recurrence4LeadingSquare_coeff_5
  recurrence4LeadingSquare_coeff_50
  recurrence4LeadingSquare_coeff_51
  recurrence4LeadingSquare_coeff_52
  recurrence4LeadingSquare_coeff_53
  recurrence4LeadingSquare_coeff_54
  recurrence4LeadingSquare_coeff_55
  recurrence4LeadingSquare_coeff_56
  recurrence4LeadingSquare_coeff_57
  recurrence4LeadingSquare_coeff_58
  recurrence4LeadingSquare_coeff_59
  recurrence4LeadingSquare_coeff_6
  recurrence4LeadingSquare_coeff_60
  recurrence4LeadingSquare_coeff_61
  recurrence4LeadingSquare_coeff_62
  recurrence4LeadingSquare_coeff_63
  recurrence4LeadingSquare_coeff_64
  recurrence4LeadingSquare_coeff_65
  recurrence4LeadingSquare_coeff_66
  recurrence4LeadingSquare_coeff_67
  recurrence4LeadingSquare_coeff_68
  recurrence4LeadingSquare_coeff_69
  recurrence4LeadingSquare_coeff_7
  recurrence4LeadingSquare_coeff_70
  recurrence4LeadingSquare_coeff_71
  recurrence4LeadingSquare_coeff_72
  recurrence4LeadingSquare_coeff_73
  recurrence4LeadingSquare_coeff_74
  recurrence4LeadingSquare_coeff_75
  recurrence4LeadingSquare_coeff_76
  recurrence4LeadingSquare_coeff_77
  recurrence4LeadingSquare_coeff_78
  recurrence4LeadingSquare_coeff_79
  recurrence4LeadingSquare_coeff_8
  recurrence4LeadingSquare_coeff_80
  recurrence4LeadingSquare_coeff_81
  recurrence4LeadingSquare_coeff_82
  recurrence4LeadingSquare_coeff_83
  recurrence4LeadingSquare_coeff_84
  recurrence4LeadingSquare_coeff_85
  recurrence4LeadingSquare_coeff_86
  recurrence4LeadingSquare_coeff_87

attribute [local simp]
  recurrence4LeadingSquare_coeff_88
  recurrence4LeadingSquare_coeff_89
  recurrence4LeadingSquare_coeff_9
  recurrence4LeadingSquare_coeff_90
  recurrence4LeadingSquare_coeff_91
  recurrence4LeadingSquare_coeff_92
  recurrence4LeadingSquare_coeff_93
  recurrence4LeadingSquare_coeff_94
  recurrence4LeadingSquare_coeff_95
  recurrence4LeadingSquare_coeff_96
  recurrence4LeadingSquare_coeff_97
  recurrence4LeadingSquare_coeff_98
  recurrence4LeadingSquare_coeff_99

private theorem recurrence4Scalar1Left_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (163 + x) *
        remainder4Coefficient1.coeff (163 - (163 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 163 + x
  · rw [recurrence4LeadingSquare_coeff_high (163 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (163 - (163 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_163 :
    recurrence4Scalar1Left.coeff 163 =
      -(((((34792 * 10 ^ 70 +
        9374637661141666657893251537187491759620261143471878023977585281630831) * 10 ^ 70 +
        6611522345150383806153571091957619453778076229245032449296873515336874) * 10 ^ 70 +
        7811852922253660510938021278402393076750572476838208292774820890283406) * 10 ^ 70 +
        9796182197503647780494569154765955785446564633008015609624710193077343) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (163 - x)) = _
  rw [show 164 = 0 +
    164 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 32 +
      36 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 36 = 32 +
      4 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 4 = 3 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_163_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (164 + x) *
        remainder4Coefficient1.coeff (164 - (164 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 164 + x
  · rw [recurrence4LeadingSquare_coeff_high (164 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (164 - (164 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_164 :
    recurrence4Scalar1Left.coeff 164 =
      (((((122022 * 10 ^ 70 +
        0057302299402328999425768403714528994271333252223598460970510198952421) * 10 ^ 70 +
        5164986774225865715985217555949617635553318853018452794962391502501689) * 10 ^ 70 +
        3946901000150704986250900265469852631222127991571989414462588652677949) * 10 ^ 70 +
        0023425089603238065483873977393186908089258421495613874111593611244401) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (164 - x)) = _
  rw [show 165 = 0 +
    165 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 32 +
      37 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 37 = 32 +
      5 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 5 = 4 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_164_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (165 + x) *
        remainder4Coefficient1.coeff (165 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 165 + x
  · rw [recurrence4LeadingSquare_coeff_high (165 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (165 - (165 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_165 :
    recurrence4Scalar1Left.coeff 165 =
      -(((((421295 * 10 ^ 70 +
        6580294467757218965977445727020562667976832646764899406140588648713989) * 10 ^ 70 +
        8796122145778512702796984094309047299426099206773756077505219025233792) * 10 ^ 70 +
        4965040952830119207443279494773123606076069641798778996983052909428051) * 10 ^ 70 +
        0479962541810780285995835462132004926825033446165810591254449337030985) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (165 - x)) = _
  rw [show 166 = 0 +
    166 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 32 +
      38 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 38 = 32 +
      6 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 6 = 5 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_165_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (166 + x) *
        remainder4Coefficient1.coeff (166 - (166 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 166 + x
  · rw [recurrence4LeadingSquare_coeff_high (166 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (166 - (166 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_166 :
    recurrence4Scalar1Left.coeff 166 =
      (((((1432084 * 10 ^ 70 +
        2848961183227165494390089232790935964164070850738755395215770244849999) * 10 ^ 70 +
        9467272969842869151112632602605712661707741252800541301862270141615130) * 10 ^ 70 +
        5010660307323983152502822923980858990217553006532285443333920347046917) * 10 ^ 70 +
        6722235288440612138805326060781757549407895407536901587684765081010885) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (166 - x)) = _
  rw [show 167 = 0 +
    167 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 32 +
      7 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_166_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (167 + x) *
        remainder4Coefficient1.coeff (167 - (167 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 167 + x
  · rw [recurrence4LeadingSquare_coeff_high (167 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (167 - (167 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_167 :
    recurrence4Scalar1Left.coeff 167 =
      -(((((4793062 * 10 ^ 70 +
        0525019286889576643510846856579521254523581411640721208646365374500960) * 10 ^ 70 +
        8546914626088142560258096897766959785731349063195882799461065531647716) * 10 ^ 70 +
        7933258074292532477520268168908119424848987550031587355883089169849238) * 10 ^ 70 +
        7577565640047218489673379197017954849714507293800326250200911318740748) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (167 - x)) = _
  rw [show 168 = 0 +
    168 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 32 +
      40 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 40 = 32 +
      8 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 8 = 7 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_167_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (168 + x) *
        remainder4Coefficient1.coeff (168 - (168 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 168 + x
  · rw [recurrence4LeadingSquare_coeff_high (168 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (168 - (168 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_168 :
    recurrence4Scalar1Left.coeff 168 =
      (((((15796090 * 10 ^ 70 +
        6972164559636109825034373834821879360837487213714694816875718297176659) * 10 ^ 70 +
        3851231166469373593885540503323883299999522220335152136595211772175795) * 10 ^ 70 +
        0191126841124333266337384330422269165851229318570428228217635477549097) * 10 ^ 70 +
        9233419386257769832145766031870781053389060239784916343311916677108976) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (168 - x)) = _
  rw [show 169 = 0 +
    169 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 32 +
      41 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 41 = 32 +
      9 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 9 = 8 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_168_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (169 + x) *
        remainder4Coefficient1.coeff (169 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 169 + x
  · rw [recurrence4LeadingSquare_coeff_high (169 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (169 - (169 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_169 :
    recurrence4Scalar1Left.coeff 169 =
      -(((((51263308 * 10 ^ 70 +
        2762583625882188615462837061206869898930428247577060024095159302128042) * 10 ^ 70 +
        9557358267240314878943933910137180360360027092993529053011339647169776) * 10 ^ 70 +
        5851979662210708804956453029183349881764279073831782120118868906711483) * 10 ^ 70 +
        3542288411421685683666067687231705470752569089976805519750781945215651) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (169 - x)) = _
  rw [show 170 = 0 +
    170 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 32 +
      42 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 42 = 32 +
      10 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 10 = 9 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_169_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (170 + x) *
        remainder4Coefficient1.coeff (170 - (170 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 170 + x
  · rw [recurrence4LeadingSquare_coeff_high (170 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (170 - (170 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_170 :
    recurrence4Scalar1Left.coeff 170 =
      (((((163836848 * 10 ^ 70 +
        0870470632800070525917342180422946122028615351346276147976962253605533) * 10 ^ 70 +
        6900021178550525695730563067620150037492885864010370546369630764332930) * 10 ^ 70 +
        7665296820337529311691974110237428337833754039820082296304172715122063) * 10 ^ 70 +
        4554447070679459302042852463624524008133585937050800973977908689911369) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (170 - x)) = _
  rw [show 171 = 0 +
    171 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 11 = 10 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_170_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (171 + x) *
        remainder4Coefficient1.coeff (171 - (171 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 171 + x
  · rw [recurrence4LeadingSquare_coeff_high (171 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (171 - (171 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_171 :
    recurrence4Scalar1Left.coeff 171 =
      -(((((515692894 * 10 ^ 70 +
        7395321055497637504294457556335620795502786987561949086413585964319627) * 10 ^ 70 +
        9450710767121188498211399235894369853595763440776932319234262252339132) * 10 ^ 70 +
        8654847712638051235609574545652498883926167697868075010487477119600469) * 10 ^ 70 +
        6971299537386108780733684967548246616899395728127917707513489448243762) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (171 - x)) = _
  rw [show 172 = 0 +
    172 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 32 +
      44 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 44 = 32 +
      12 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 12 = 11 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_171_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (172 + x) *
        remainder4Coefficient1.coeff (172 - (172 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 172 + x
  · rw [recurrence4LeadingSquare_coeff_high (172 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (172 - (172 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_172 :
    recurrence4Scalar1Left.coeff 172 =
      (((((1598715437 * 10 ^ 70 +
        8431004007587056549076088858559143711250919414509945268319961795261143) * 10 ^ 70 +
        6835570117712310802022479627278757052344161688675201302795894504072808) * 10 ^ 70 +
        8946112238246439444999082996933445595469211487584413636291886249945957) * 10 ^ 70 +
        0245763076130643811153606738911925740347302729173229809917408284480429) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (172 - x)) = _
  rw [show 173 = 0 +
    173 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 32 +
      45 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 45 = 32 +
      13 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 13 = 12 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_172_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (173 + x) *
        remainder4Coefficient1.coeff (173 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 173 + x
  · rw [recurrence4LeadingSquare_coeff_high (173 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (173 - (173 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_173 :
    recurrence4Scalar1Left.coeff 173 =
      -(((((4881763037 * 10 ^ 70 +
        8341670977898171966987053004198412738210338936802368371401588543319895) * 10 ^ 70 +
        1219938796130574163941192205019085813195927500822236707403209710348235) * 10 ^ 70 +
        5159658205308986687882111063199274122583069238765599541907654900011489) * 10 ^ 70 +
        5684830632173984491288876512219147296875874021951470513859598849795512) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (173 - x)) = _
  rw [show 174 = 0 +
    174 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 32 +
      46 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 46 = 32 +
      14 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 14 = 13 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_173_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (174 + x) *
        remainder4Coefficient1.coeff (174 - (174 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 174 + x
  · rw [recurrence4LeadingSquare_coeff_high (174 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (174 - (174 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_174 :
    recurrence4Scalar1Left.coeff 174 =
      (((((14683581127 * 10 ^ 70 +
        3353598851369147458126815668580582308975013259355364206821075149938760) * 10 ^ 70 +
        9854869203809760512568918955140813784813933975172174897351690898279888) * 10 ^ 70 +
        9054593318398603211467924100881388309663728913037090978466474150187726) * 10 ^ 70 +
        3306661409212967636035717419442532188546493490497231205394566623192803) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (174 - x)) = _
  rw [show 175 = 0 +
    175 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 15 = 14 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_174_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (175 + x) *
        remainder4Coefficient1.coeff (175 - (175 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 175 + x
  · rw [recurrence4LeadingSquare_coeff_high (175 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (175 - (175 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_175 :
    recurrence4Scalar1Left.coeff 175 =
      -(((((43507139893 * 10 ^ 70 +
        5513166541890910005146809157883752227486005738842559800224009985986412) * 10 ^ 70 +
        0996029751240510955924699565814523516909660779508997182183777108116523) * 10 ^ 70 +
        0597243455607399783000915831218723813118768276672186372261953570151195) * 10 ^ 70 +
        4576787014975818912254978299319860310682390993725118256657813755431776) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (175 - x)) = _
  rw [show 176 = 0 +
    176 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 32 +
      48 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 48 = 32 +
      16 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 16 = 15 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_175_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (176 + x) *
        remainder4Coefficient1.coeff (176 - (176 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 176 + x
  · rw [recurrence4LeadingSquare_coeff_high (176 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (176 - (176 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_176 :
    recurrence4Scalar1Left.coeff 176 =
      (((((126994544981 * 10 ^ 70 +
        6374119168941853724994522113447271134619932647183812066197597956948550) * 10 ^ 70 +
        7339811438722381724679590482631897991492108007230762184161875617947307) * 10 ^ 70 +
        3825334321106267119232898375871592719212168130742776024492444825568031) * 10 ^ 70 +
        2631496193856339168585177393868733658660877534522805519000689224578685) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (176 - x)) = _
  rw [show 177 = 0 +
    177 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 32 +
      49 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 49 = 32 +
      17 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 17 = 16 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_176_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (177 + x) *
        remainder4Coefficient1.coeff (177 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 177 + x
  · rw [recurrence4LeadingSquare_coeff_high (177 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (177 - (177 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_177 :
    recurrence4Scalar1Left.coeff 177 =
      -(((((365197307807 * 10 ^ 70 +
        0434877041053632362981276659867199533305104430075479193371071318913317) * 10 ^ 70 +
        9912700663225962621769382425010979186319810582855633916002797293013944) * 10 ^ 70 +
        6754465577370470086006321002407046227930488680959383047186729618422262) * 10 ^ 70 +
        2994094802766404461338837470086167352198745357020579932182859639762248) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (177 - x)) = _
  rw [show 178 = 0 +
    178 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 32 +
      50 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 50 = 32 +
      18 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 18 = 17 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_177_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (178 + x) *
        remainder4Coefficient1.coeff (178 - (178 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 178 + x
  · rw [recurrence4LeadingSquare_coeff_high (178 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (178 - (178 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_178 :
    recurrence4Scalar1Left.coeff 178 =
      (((((1034687701277 * 10 ^ 70 +
        4883325709053272561050458100617612719714818983830382679202077682235212) * 10 ^ 70 +
        6319838256345073386921128885471106678835432836835093118186463402016578) * 10 ^ 70 +
        6412198267657559173281009112034502594420558175268774599276016501662135) * 10 ^ 70 +
        9865794053500412102657332728745970886584253898577507387011415146443830) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (178 - x)) = _
  rw [show 179 = 0 +
    179 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_178_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (179 + x) *
        remainder4Coefficient1.coeff (179 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 179 + x
  · rw [recurrence4LeadingSquare_coeff_high (179 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (179 - (179 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_179 :
    recurrence4Scalar1Left.coeff 179 =
      -(((((2888356209989 * 10 ^ 70 +
        8686736624324390578057403371424162130033352625442954685075167603933227) * 10 ^ 70 +
        6323700216796903783159778131073606922477472790660318700956242844411984) * 10 ^ 70 +
        3278432297585045361149036991284466335891218626357363615030511315804728) * 10 ^ 70 +
        2773545993542752740283922041575007565296749699657464875004807531873197) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (179 - x)) = _
  rw [show 180 = 0 +
    180 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 32 +
      52 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 52 = 32 +
      20 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 20 = 19 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_179_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (180 + x) *
        remainder4Coefficient1.coeff (180 - (180 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 180 + x
  · rw [recurrence4LeadingSquare_coeff_high (180 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (180 - (180 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_180 :
    recurrence4Scalar1Left.coeff 180 =
      (((((7944595268431 * 10 ^ 70 +
        9884787082481753525149403806492616669277917058042929675794701895526955) * 10 ^ 70 +
        4370920810048518282919310688280263018856395141613041468051897021762057) * 10 ^ 70 +
        0468549087191305670330766477057465130044764188143678444104148475891341) * 10 ^ 70 +
        0441753665502285367369018416627448850512271494022137185289453198263165) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (180 - x)) = _
  rw [show 181 = 0 +
    181 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 32 +
      53 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 53 = 32 +
      21 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 21 = 20 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_180_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (181 + x) *
        remainder4Coefficient1.coeff (181 - (181 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 181 + x
  · rw [recurrence4LeadingSquare_coeff_high (181 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (181 - (181 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_181 :
    recurrence4Scalar1Left.coeff 181 =
      -(((((21532352170079 * 10 ^ 70 +
        5868209184959695635257279412085109895472879749200444242564245279568291) * 10 ^ 70 +
        9889956495326566589645367713061754829394764296475484010937309479374587) * 10 ^ 70 +
        4919854367955273573372636279313267403641197175125915129871308477454207) * 10 ^ 70 +
        8425208349134372930490958899898148803206282109804109374664010434597438) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (181 - x)) = _
  rw [show 182 = 0 +
    182 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_181_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (182 + x) *
        remainder4Coefficient1.coeff (182 - (182 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 182 + x
  · rw [recurrence4LeadingSquare_coeff_high (182 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (182 - (182 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_182 :
    recurrence4Scalar1Left.coeff 182 =
      (((((57507999576507 * 10 ^ 70 +
        7464998473934392538026536422821734709708842437867201664976103827469023) * 10 ^ 70 +
        3189423403590782436530863778310335397699863728391914110974268836761403) * 10 ^ 70 +
        9413749539797680697446943244283857640654852225402545836446512636456019) * 10 ^ 70 +
        2489120018553138814735062613727108101941384159945834276058440507295369) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (182 - x)) = _
  rw [show 183 = 0 +
    183 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 32 +
      23 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 23 = 22 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_182_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (183 + x) *
        remainder4Coefficient1.coeff (183 - (183 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 183 + x
  · rw [recurrence4LeadingSquare_coeff_high (183 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (183 - (183 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_183 :
    recurrence4Scalar1Left.coeff 183 =
      -(((((151356079285170 * 10 ^ 70 +
        0329924244464087443735656692860384572863371723430490854750434733472496) * 10 ^ 70 +
        4061923209683879578830864892562843570495071999107224958907516128360285) * 10 ^ 70 +
        6584667305635356958516914610942513010241906523322295262074360557681119) * 10 ^ 70 +
        6377957175326652270351190149651518489256805144957739561909488891667107) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (183 - x)) = _
  rw [show 184 = 0 +
    184 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 32 +
      56 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 56 = 32 +
      24 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 24 = 23 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_183_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (184 + x) *
        remainder4Coefficient1.coeff (184 - (184 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 184 + x
  · rw [recurrence4LeadingSquare_coeff_high (184 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (184 - (184 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_184 :
    recurrence4Scalar1Left.coeff 184 =
      (((((392575645258974 * 10 ^ 70 +
        7690347444891429102833923162034798599148574930090418231712924953305822) * 10 ^ 70 +
        1983108151767553543923899367415601652405998026069286643405314444973967) * 10 ^ 70 +
        3334903072378111425901602866961521403994648937732705006371110440098739) * 10 ^ 70 +
        3242677900704637784739010799162136394735797376968520382346251982971132) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (184 - x)) = _
  rw [show 185 = 0 +
    185 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 32 +
      57 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 57 = 32 +
      25 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 25 = 24 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_184_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (185 + x) *
        remainder4Coefficient1.coeff (185 - (185 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 185 + x
  · rw [recurrence4LeadingSquare_coeff_high (185 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (185 - (185 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_185 :
    recurrence4Scalar1Left.coeff 185 =
      -(((((1003494725974045 * 10 ^ 70 +
        2108571508639970633133831711328061675779086343730569398551414854943791) * 10 ^ 70 +
        3766391814797973428252045258346691736805183998976083661977473926967761) * 10 ^ 70 +
        2288944419568589722836280173200528269229932147537662003664323316855345) * 10 ^ 70 +
        2032993111057676563828711331622955783534634125128332275371494037941042) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (185 - x)) = _
  rw [show 186 = 0 +
    186 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
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
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_185_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (186 + x) *
        remainder4Coefficient1.coeff (186 - (186 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 186 + x
  · rw [recurrence4LeadingSquare_coeff_high (186 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (186 - (186 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_186 :
    recurrence4Scalar1Left.coeff 186 =
      (((((2528079971442100 * 10 ^ 70 +
        4483240304845749345545214626132497532794362867861617652679678373205083) * 10 ^ 70 +
        4084636783939725487155428569367685771121610875731735826654041953942256) * 10 ^ 70 +
        0038260165075662410948519308809262384257726476580787678512250581606097) * 10 ^ 70 +
        5324112133593848564742046165495115364615987088351625496702603422460816) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (186 - x)) = _
  rw [show 187 = 0 +
    187 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 187 = 32 +
      155 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 155 = 32 +
      123 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 123 = 32 +
      91 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 91 = 32 +
      59 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 59 = 32 +
      27 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 27 = 26 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_186_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (187 + x) *
        remainder4Coefficient1.coeff (187 - (187 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 187 + x
  · rw [recurrence4LeadingSquare_coeff_high (187 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (187 - (187 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_187 :
    recurrence4Scalar1Left.coeff 187 =
      -(((((6277193953641014 * 10 ^ 70 +
        0362509822339505201334497626565835518280918479282134743349339600164232) * 10 ^ 70 +
        0073710539345187997980242076055834674363094096275888446497779819401039) * 10 ^ 70 +
        9421824336739716473105653395486990646984238188316182755600794058014988) * 10 ^ 70 +
        1360859257133219395085262746622257385269185074246220812026780262756417) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (187 - x)) = _
  rw [show 188 = 0 +
    188 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 188 = 32 +
      156 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 156 = 32 +
      124 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 124 = 32 +
      92 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 92 = 32 +
      60 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 60 = 32 +
      28 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 28 = 27 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_187_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (188 + x) *
        remainder4Coefficient1.coeff (188 - (188 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 188 + x
  · rw [recurrence4LeadingSquare_coeff_high (188 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (188 - (188 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_188 :
    recurrence4Scalar1Left.coeff 188 =
      (((((15362210413687424 * 10 ^ 70 +
        5515548815323999233059967268240801304812166653241479661527609138679621) * 10 ^ 70 +
        4969135573303367573581185371577025936299570452372273168134148848279397) * 10 ^ 70 +
        6595034127060108786065730241607158107671292041315455182530505039392853) * 10 ^ 70 +
        4360143575872870344518693435033498511243653271922320661030607866831530) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (188 - x)) = _
  rw [show 189 = 0 +
    189 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 189 = 32 +
      157 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 157 = 32 +
      125 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 125 = 32 +
      93 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 93 = 32 +
      61 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 61 = 32 +
      29 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 29 = 28 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_188_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (189 + x) *
        remainder4Coefficient1.coeff (189 - (189 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 189 + x
  · rw [recurrence4LeadingSquare_coeff_high (189 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (189 - (189 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_189 :
    recurrence4Scalar1Left.coeff 189 =
      -(((((37056895523871852 * 10 ^ 70 +
        0298950300590912001100224181487398592972266197681274248401058311323123) * 10 ^ 70 +
        1353751103654122144531957167163825515342946739562512383826595953672725) * 10 ^ 70 +
        6151964343611309347359218270957233492686180812634809619060828501469687) * 10 ^ 70 +
        8310004554198639629258993180537602836250382306771538397705629731983333) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (189 - x)) = _
  rw [show 190 = 0 +
    190 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 190 = 32 +
      158 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 158 = 32 +
      126 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 126 = 32 +
      94 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 94 = 32 +
      62 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 62 = 32 +
      30 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 30 = 29 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_189_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (190 + x) *
        remainder4Coefficient1.coeff (190 - (190 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 190 + x
  · rw [recurrence4LeadingSquare_coeff_high (190 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (190 - (190 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_190 :
    recurrence4Scalar1Left.coeff 190 =
      (((((88109879314514851 * 10 ^ 70 +
        9843554819586738825317762233630387339515918902228194764345629890296879) * 10 ^ 70 +
        0301951102078296286770280112209485443211328020103052101879026542288171) * 10 ^ 70 +
        4166233730356393979940506041887002874041537019913006396458719683926388) * 10 ^ 70 +
        6475533827045767950328190196980098155576996659647657570577011690741018) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (190 - x)) = _
  rw [show 191 = 0 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_190_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (191 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (191 + x) *
        remainder4Coefficient1.coeff (191 - (191 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 191 + x
  · rw [recurrence4LeadingSquare_coeff_high (191 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (191 - (191 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_191 :
    recurrence4Scalar1Left.coeff 191 =
      -(((((206506090037817514 * 10 ^ 70 +
        4058446738071562075654812090597901386737061856024767936549223899557980) * 10 ^ 70 +
        0114052035198444547446194196729280603914808623926543291187212503659387) * 10 ^ 70 +
        0745655178506406643491808209967511557209060823114732754584224193647432) * 10 ^ 70 +
        5939812966394803025651469838609908229812990375011960298879223400789924) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (191 - x)) = _
  rw [show 192 = 1 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_191_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (192 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (192 + x) *
        remainder4Coefficient1.coeff (192 - (192 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 192 + x
  · rw [recurrence4LeadingSquare_coeff_high (192 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (192 - (192 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_192 :
    recurrence4Scalar1Left.coeff 192 =
      (((((477095793540426003 * 10 ^ 70 +
        2465654270478701025095312240073055182745588959996221552363898954684659) * 10 ^ 70 +
        3959747041458917973836793970579784684663325083482234002288631234654006) * 10 ^ 70 +
        5906013292337706679558635379562021217547614321297686148284642912796779) * 10 ^ 70 +
        2910434363426154964186217501373806709595527220721128516850517351704347) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (192 - x)) = _
  rw [show 193 = 2 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_192_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar1Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (193 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (193 + x) *
        remainder4Coefficient1.coeff (193 - (193 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 193 + x
  · rw [recurrence4LeadingSquare_coeff_high (193 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (193 - (193 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_193 :
    recurrence4Scalar1Left.coeff 193 =
      -(((((1086560479553661432 * 10 ^ 70 +
        3433785298765415578611787441276677897199721144084091727689097911079343) * 10 ^ 70 +
        7520479719229386218810324691920724464862579392133458654599089227968403) * 10 ^ 70 +
        0528755489303432468779986656983720071668365150372684428021686784711718) * 10 ^ 70 +
        7278710863858952962458966992949409831706153312720796387881890888618653) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (193 - x)) = _
  rw [show 194 = 3 +
    191 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 191 = 32 +
      159 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 159 = 32 +
      127 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 127 = 32 +
      95 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 95 = 32 +
      63 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 63 = 32 +
      31 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 31 = 30 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar1Left_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_193_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
