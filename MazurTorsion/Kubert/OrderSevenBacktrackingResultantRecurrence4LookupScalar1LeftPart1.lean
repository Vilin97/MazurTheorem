/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (194 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (194 + x) *
        remainder4Coefficient1.coeff (194 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 194 + x
  · rw [recurrence4LeadingSquare_coeff_high (194 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (194 - (194 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_194 :
    recurrence4Scalar1Left.coeff 194 =
      (((((2439429584864258550 * 10 ^ 70 +
        5974251269071649414568607468576126577892543286824553282738653520645180) * 10 ^ 70 +
        9068345037864762610394711679731026030433399683635939246524433744813269) * 10 ^ 70 +
        1938867338681062216141053325709353897613825717704485066203781676473648) * 10 ^ 70 +
        0104287257406671291098155383904715930385211227326373990728798741907234) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (194 - x)) = _
  rw [show 195 = 4 +
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
  rw [recurrence4Scalar1Left_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (195 + x) *
        remainder4Coefficient1.coeff (195 - (195 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 195 + x
  · rw [recurrence4LeadingSquare_coeff_high (195 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (195 - (195 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_195 :
    recurrence4Scalar1Left.coeff 195 =
      -(((((5399064833105940927 * 10 ^ 70 +
        4843741165992093254681976129816583032504977646939415404199633940421855) * 10 ^ 70 +
        5533363045683187711567844977996105960575208932619170104246723655940671) * 10 ^ 70 +
        6470252058887380700921891333217982315821364366777234442249196872243913) * 10 ^ 70 +
        5686027963239069117851990598619018801424996802174010579390291070993620) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (195 - x)) = _
  rw [show 196 = 5 +
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
  rw [recurrence4Scalar1Left_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (196 + x) *
        remainder4Coefficient1.coeff (196 - (196 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 196 + x
  · rw [recurrence4LeadingSquare_coeff_high (196 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (196 - (196 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_196 :
    recurrence4Scalar1Left.coeff 196 =
      (((((11780231274144312248 * 10 ^ 70 +
        7303654491759973140810563737361002500695446852330012465083490751657523) * 10 ^ 70 +
        8721552894371063735567834940988721983387554073510200455079721618522847) * 10 ^ 70 +
        5399049641392117147662019117736816421999698688474171411412283756513807) * 10 ^ 70 +
        7590962769287636039142657791078749249088161565536766579960391578829813) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (196 - x)) = _
  rw [show 197 = 6 +
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
  rw [recurrence4Scalar1Left_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (197 + x) *
        remainder4Coefficient1.coeff (197 - (197 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 197 + x
  · rw [recurrence4LeadingSquare_coeff_high (197 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (197 - (197 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_197 :
    recurrence4Scalar1Left.coeff 197 =
      -(((((25339764831791542572 * 10 ^ 70 +
        0192847501231896492198134144502308885953952592575129332238091622573507) * 10 ^ 70 +
        7370465692078005945544301867973853664190625169849393410460342445149891) * 10 ^ 70 +
        1177517140248245294027690261844680498122558282354414755874025996815858) * 10 ^ 70 +
        0449154642970733160474022581912876428699657056449206815410609108567886) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (197 - x)) = _
  rw [show 198 = 7 +
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
  rw [recurrence4Scalar1Left_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (198 + x) *
        remainder4Coefficient1.coeff (198 - (198 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 198 + x
  · rw [recurrence4LeadingSquare_coeff_high (198 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (198 - (198 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_198 :
    recurrence4Scalar1Left.coeff 198 =
      (((((53736901652559926368 * 10 ^ 70 +
        1397105875004104200966127321406309477926272399262805375811510241120125) * 10 ^ 70 +
        3252807072940576374457353583247930288278894701773233776865218067414026) * 10 ^ 70 +
        8855393916326722156674548688759755737885295089139747974721070145533458) * 10 ^ 70 +
        5462470086615531937542143637660297478984991639803295082356195101195668) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (198 - x)) = _
  rw [show 199 = 8 +
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
  rw [recurrence4Scalar1Left_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (199 + x) *
        remainder4Coefficient1.coeff (199 - (199 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 199 + x
  · rw [recurrence4LeadingSquare_coeff_high (199 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (199 - (199 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_199 :
    recurrence4Scalar1Left.coeff 199 =
      -(((((112349473828217846838 * 10 ^ 70 +
        3154104883091498248171932605177077538621877691368890520729780841097549) * 10 ^ 70 +
        3369943005224580730582450371082070886950553486051093801373445251543720) * 10 ^ 70 +
        3395185732376106141308032894464476677564531378785684263607536889863825) * 10 ^ 70 +
        3427231765973383004947071386031068534285185607997992310135793580041837) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (199 - x)) = _
  rw [show 200 = 9 +
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
  rw [recurrence4Scalar1Left_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (200 + x) *
        remainder4Coefficient1.coeff (200 - (200 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 200 + x
  · rw [recurrence4LeadingSquare_coeff_high (200 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (200 - (200 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_200 :
    recurrence4Scalar1Left.coeff 200 =
      (((((231581700041044205172 * 10 ^ 70 +
        4882533681705870172643414607815397935290486364588046693879178029308386) * 10 ^ 70 +
        6350537443057169282043419690396380841820274873451339628630282436557215) * 10 ^ 70 +
        1151600763613827360690238080141552638097774071580431762500139252780744) * 10 ^ 70 +
        6705486353219264702131738822638564725760277152554347334722008974819985) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (200 - x)) = _
  rw [show 201 = 10 +
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
  rw [recurrence4Scalar1Left_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (201 + x) *
        remainder4Coefficient1.coeff (201 - (201 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 201 + x
  · rw [recurrence4LeadingSquare_coeff_high (201 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (201 - (201 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_201 :
    recurrence4Scalar1Left.coeff 201 =
      -(((((470628136120986800412 * 10 ^ 70 +
        2662896966837852156769145918013590794762211478176208382242722865512467) * 10 ^ 70 +
        7274717524903593868006889691535129220934818854900993624969378789711736) * 10 ^ 70 +
        9121625102880361425015249749564138499606003831134602372731129252400365) * 10 ^ 70 +
        1467349205825686196886994501823069902407885749324161453981190719250396) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (201 - x)) = _
  rw [show 202 = 11 +
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
  rw [recurrence4Scalar1Left_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (202 + x) *
        remainder4Coefficient1.coeff (202 - (202 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 202 + x
  · rw [recurrence4LeadingSquare_coeff_high (202 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (202 - (202 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_202 :
    recurrence4Scalar1Left.coeff 202 =
      (((((942967968961878166220 * 10 ^ 70 +
        8087966145524044869200635985177276237640387258097751195512664572643193) * 10 ^ 70 +
        7086562183026513222604524318088469619137429580873839418135899703595362) * 10 ^ 70 +
        6332874704162733576206007220835977743790363090019497635680768528148675) * 10 ^ 70 +
        5685474491433703783302505720632250629808039013972305918234055757454553) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (202 - x)) = _
  rw [show 203 = 12 +
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
  rw [recurrence4Scalar1Left_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (203 + x) *
        remainder4Coefficient1.coeff (203 - (203 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 203 + x
  · rw [recurrence4LeadingSquare_coeff_high (203 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (203 - (203 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_203 :
    recurrence4Scalar1Left.coeff 203 =
      -(((((1862797284498587583944 * 10 ^ 70 +
        4690878155864982770973675098415615195648944778182048709151300276716715) * 10 ^ 70 +
        4854204387078249532005896147540632612289217213956773660849369149152017) * 10 ^ 70 +
        5272591709475718676521710140616391067400805579776347162526233117831043) * 10 ^ 70 +
        6647723619936057677143223720105201471046664482890929270378632654753485) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (203 - x)) = _
  rw [show 204 = 13 +
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
  rw [recurrence4Scalar1Left_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (204 + x) *
        remainder4Coefficient1.coeff (204 - (204 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 204 + x
  · rw [recurrence4LeadingSquare_coeff_high (204 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (204 - (204 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_204 :
    recurrence4Scalar1Left.coeff 204 =
      (((((3628167115877686284751 * 10 ^ 70 +
        9118865079122004700526702586616701246261972328970715312264012555589780) * 10 ^ 70 +
        9974081073814804663641357238746138543874255195222045344080330930789695) * 10 ^ 70 +
        9965647753487818401199750300347409134881292264055896855820469355534460) * 10 ^ 70 +
        7073602918592399185993340007530203482626554881226464635960863080980599) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (204 - x)) = _
  rw [show 205 = 14 +
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
  rw [recurrence4Scalar1Left_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (205 + x) *
        remainder4Coefficient1.coeff (205 - (205 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 205 + x
  · rw [recurrence4LeadingSquare_coeff_high (205 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (205 - (205 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_205 :
    recurrence4Scalar1Left.coeff 205 =
      -(((((6967302012910106664840 * 10 ^ 70 +
        2836199281155948256574790511128667974156807339433665349820321973709002) * 10 ^ 70 +
        8736684474366234491530213451293117514825582114009754860153236990273751) * 10 ^ 70 +
        8996836939157893073610271076252894146402575493889357338412740769123912) * 10 ^ 70 +
        3996118399566548558293122089851348015865053210785535813867159565389455) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (205 - x)) = _
  rw [show 206 = 15 +
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
  rw [recurrence4Scalar1Left_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (206 + x) *
        remainder4Coefficient1.coeff (206 - (206 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 206 + x
  · rw [recurrence4LeadingSquare_coeff_high (206 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (206 - (206 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_206 :
    recurrence4Scalar1Left.coeff 206 =
      (((((13191660749085028156455 * 10 ^ 70 +
        3067152911084270689251585572399182035019379841385511065334691128451742) * 10 ^ 70 +
        4147050335225556586554823621316332671578625902790147179707490220018053) * 10 ^ 70 +
        7451780168168984341520644956273031026500003050186637904430621203067780) * 10 ^ 70 +
        8678139511044403385904246729768287763247447400398654703541898515139233) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (206 - x)) = _
  rw [show 207 = 16 +
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
  rw [recurrence4Scalar1Left_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (207 + x) *
        remainder4Coefficient1.coeff (207 - (207 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 207 + x
  · rw [recurrence4LeadingSquare_coeff_high (207 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (207 - (207 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_207 :
    recurrence4Scalar1Left.coeff 207 =
      -(((((24625937014718956895102 * 10 ^ 70 +
        3718942987234060960068279385720601010823108461627349447212540051324204) * 10 ^ 70 +
        8737538856512516467055988683396282947652025531106359670684186698260793) * 10 ^ 70 +
        2853370979314626183775477507761483979594807679586271221029491683752059) * 10 ^ 70 +
        7056343691233348262181313076563919281689073394730557065045921350405628) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (207 - x)) = _
  rw [show 208 = 17 +
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
  rw [recurrence4Scalar1Left_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (208 + x) *
        remainder4Coefficient1.coeff (208 - (208 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 208 + x
  · rw [recurrence4LeadingSquare_coeff_high (208 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (208 - (208 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_208 :
    recurrence4Scalar1Left.coeff 208 =
      (((((45325707856198279052263 * 10 ^ 70 +
        4002325296589066712444438928578180352229269225729267864090245004634211) * 10 ^ 70 +
        1991060008137246900007325550523483127693961027507055558088417964394996) * 10 ^ 70 +
        8992984678531067619207140214514430801204773787416089546557809767730515) * 10 ^ 70 +
        7915435966088469972466039567596874197698283181189161562964131091056027) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (208 - x)) = _
  rw [show 209 = 18 +
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
  rw [recurrence4Scalar1Left_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (209 + x) *
        remainder4Coefficient1.coeff (209 - (209 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 209 + x
  · rw [recurrence4LeadingSquare_coeff_high (209 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (209 - (209 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_209 :
    recurrence4Scalar1Left.coeff 209 =
      -(((((82253452627604768035473 * 10 ^ 70 +
        6162432070862380729327614327513083648062512431389487509920449842940113) * 10 ^ 70 +
        6780297593104746448283409316827316760981416371380227971331147381719933) * 10 ^ 70 +
        6299345990056108818192386860087379410263700211072071467930711974780887) * 10 ^ 70 +
        4052628814318609343733467865505200940219015676253375775996689407820078) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (209 - x)) = _
  rw [show 210 = 19 +
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
  rw [recurrence4Scalar1Left_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (210 + x) *
        remainder4Coefficient1.coeff (210 - (210 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 210 + x
  · rw [recurrence4LeadingSquare_coeff_high (210 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (210 - (210 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_210 :
    recurrence4Scalar1Left.coeff 210 =
      (((((147170105052868200755625 * 10 ^ 70 +
        0927711564172320942716876478712958769866373856229439384733361384757329) * 10 ^ 70 +
        3632735372719144814526336767479535000100831076333184349185188623633347) * 10 ^ 70 +
        2356534125660382477366083620116144164638500395326916127216027841874101) * 10 ^ 70 +
        4559391577649744874961128782813926241292272730666359723133288467067145) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (210 - x)) = _
  rw [show 211 = 20 +
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
  rw [recurrence4Scalar1Left_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (211 + x) *
        remainder4Coefficient1.coeff (211 - (211 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 211 + x
  · rw [recurrence4LeadingSquare_coeff_high (211 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (211 - (211 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_211 :
    recurrence4Scalar1Left.coeff 211 =
      -(((((259620026981011082279831 * 10 ^ 70 +
        4955362209508305721378260416587754743132427509481809596817147828255170) * 10 ^ 70 +
        8023842946189758627739413290980312312583258318670460413255066169778946) * 10 ^ 70 +
        0217395968635688282768818214606462358365172756353245317171470797651902) * 10 ^ 70 +
        2174524950643525279983679428979584710480524955559633217210202192400777) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (211 - x)) = _
  rw [show 212 = 21 +
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
  rw [recurrence4Scalar1Left_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (212 + x) *
        remainder4Coefficient1.coeff (212 - (212 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 212 + x
  · rw [recurrence4LeadingSquare_coeff_high (212 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (212 - (212 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_212 :
    recurrence4Scalar1Left.coeff 212 =
      (((((451550220178772671328009 * 10 ^ 70 +
        7760074631735583304774119393912770263470403103342500690804472361159239) * 10 ^ 70 +
        5869242345303652239520254792262420927643145062814366989226033328726745) * 10 ^ 70 +
        8614592146699764534319214569072519184529619027504464559616585944658296) * 10 ^ 70 +
        3786736698942063445292920097932860541708635309343397514984440336587682) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (212 - x)) = _
  rw [show 213 = 22 +
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
  rw [recurrence4Scalar1Left_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (213 + x) *
        remainder4Coefficient1.coeff (213 - (213 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 213 + x
  · rw [recurrence4LeadingSquare_coeff_high (213 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (213 - (213 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_213 :
    recurrence4Scalar1Left.coeff 213 =
      -(((((774316006981363451158638 * 10 ^ 70 +
        7997980867175673381009852331057161570411606210830009372525733869085615) * 10 ^ 70 +
        8623323764235821845283629327647211654171061397182833936013861368408808) * 10 ^ 70 +
        2829650062587784810851002153882949285994724788011011315877924063019755) * 10 ^ 70 +
        6872999533164699244775149413263455864341478767491019585891638585839349) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (213 - x)) = _
  rw [show 214 = 23 +
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
  rw [recurrence4Scalar1Left_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (214 + x) *
        remainder4Coefficient1.coeff (214 - (214 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 214 + x
  · rw [recurrence4LeadingSquare_coeff_high (214 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (214 - (214 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_214 :
    recurrence4Scalar1Left.coeff 214 =
      (((((1309087216933670259450334 * 10 ^ 70 +
        2633886357865705575592661356308308552583245255739607519006756873516891) * 10 ^ 70 +
        5582271831451554301165953299483587491005115746633452022198647295396312) * 10 ^ 70 +
        2037960971316814976632929843689530747215236563451109006356642614721149) * 10 ^ 70 +
        1622763335503690397001133848412273548535442225533288541595045175986903) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (214 - x)) = _
  rw [show 215 = 24 +
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
  rw [recurrence4Scalar1Left_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (215 + x) *
        remainder4Coefficient1.coeff (215 - (215 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 215 + x
  · rw [recurrence4LeadingSquare_coeff_high (215 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (215 - (215 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_215 :
    recurrence4Scalar1Left.coeff 215 =
      -(((((2181974619815149598588142 * 10 ^ 70 +
        6867212330329156901420659680861011799002365956644358599049924798700163) * 10 ^ 70 +
        7118266078280487690299452121577547411678923061688675872887257177426879) * 10 ^ 70 +
        3426170020530150267120792247324116579444291799176195106215332250082233) * 10 ^ 70 +
        0553385568804632894355046790467378037946567600808850803685828588774076) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (215 - x)) = _
  rw [show 216 = 25 +
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
  rw [recurrence4Scalar1Left_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (216 + x) *
        remainder4Coefficient1.coeff (216 - (216 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 216 + x
  · rw [recurrence4LeadingSquare_coeff_high (216 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (216 - (216 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_216 :
    recurrence4Scalar1Left.coeff 216 =
      (((((3585525721847991432609740 * 10 ^ 70 +
        0712771556697673180704368865636001310411527782706190011332384803607622) * 10 ^ 70 +
        1238289162039932847207645111940705246005352269209668412122650884831346) * 10 ^ 70 +
        3905193962850396929844051363168810073576015546289543422412190034233372) * 10 ^ 70 +
        1988798067238795185728329650846100619431229514347255888331820424940879) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (216 - x)) = _
  rw [show 217 = 26 +
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
  rw [recurrence4Scalar1Left_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (217 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (217 + x) *
        remainder4Coefficient1.coeff (217 - (217 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 217 + x
  · rw [recurrence4LeadingSquare_coeff_high (217 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (217 - (217 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_217 :
    recurrence4Scalar1Left.coeff 217 =
      -(((((5808551782378781385000361 * 10 ^ 70 +
        5515915972007080171178640167365561788051889243887799819029761644079671) * 10 ^ 70 +
        5301041330187369539892550516875651124056795190399891426387742278418427) * 10 ^ 70 +
        5078073070517574345687324951732552047874214756069079164313076473262476) * 10 ^ 70 +
        3705414337253087195797644098621970822282479323644512128778756209517840) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (217 - x)) = _
  rw [show 218 = 27 +
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
  rw [recurrence4Scalar1Left_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (218 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (218 + x) *
        remainder4Coefficient1.coeff (218 - (218 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 218 + x
  · rw [recurrence4LeadingSquare_coeff_high (218 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (218 - (218 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_218 :
    recurrence4Scalar1Left.coeff 218 =
      (((((9276477009846557303045137 * 10 ^ 70 +
        3711743762459646265976113125710781168092159903978421357911796358963645) * 10 ^ 70 +
        4963446782017398101463111206337047398470222084815699198437020062415051) * 10 ^ 70 +
        1528393925909536696736355915252595879673494102540051642686826294336025) * 10 ^ 70 +
        8641400209871084595036565990901396957630666867623952924922267022344842) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (218 - x)) = _
  rw [show 219 = 28 +
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
  rw [recurrence4Scalar1Left_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (219 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (219 + x) *
        remainder4Coefficient1.coeff (219 - (219 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 219 + x
  · rw [recurrence4LeadingSquare_coeff_high (219 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (219 - (219 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_219 :
    recurrence4Scalar1Left.coeff 219 =
      -(((((14604447233492179593320992 * 10 ^ 70 +
        8327198686741827756264889302258092450125064859014150780527415199465430) * 10 ^ 70 +
        4170017770636027195844456079057174994391910469168336793617099156847526) * 10 ^ 70 +
        2888034943276865430997595682319325808716284785420066982727316523981168) * 10 ^ 70 +
        7343183682540719369753365744906830550153966572741089071309051055641521) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (219 - x)) = _
  rw [show 220 = 29 +
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
  rw [recurrence4Scalar1Left_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (220 + x) *
        remainder4Coefficient1.coeff (220 - (220 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 220 + x
  · rw [recurrence4LeadingSquare_coeff_high (220 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (220 - (220 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_220 :
    recurrence4Scalar1Left.coeff 220 =
      (((((22665165613312500531640290 * 10 ^ 70 +
        7452893137472705705030300492664312689798351073091117860888714660016427) * 10 ^ 70 +
        2749651842766103644694349523468106527893821512121115637691039919641505) * 10 ^ 70 +
        4295936933322228814745132548489414952292651405348022668382401474412299) * 10 ^ 70 +
        0419284408416981514873421402396516156053219573008428931263581240088402) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (220 - x)) = _
  rw [show 221 = 30 +
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
  rw [recurrence4Scalar1Left_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (221 + x) *
        remainder4Coefficient1.coeff (221 - (221 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 221 + x
  · rw [recurrence4LeadingSquare_coeff_high (221 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (221 - (221 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_221 :
    recurrence4Scalar1Left.coeff 221 =
      -(((((34672673842289262721636449 * 10 ^ 70 +
        0292544470977788371719552443180174275903623430215594294035122732444020) * 10 ^ 70 +
        4084960229358266682217778583440781234383012366075677906846939260347345) * 10 ^ 70 +
        9199674844965606427163353935033057253886964382481590288978151634256420) * 10 ^ 70 +
        5715868559701875770778795245374794911342424718109457085645519725359770) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (221 - x)) = _
  rw [show 222 = 31 +
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
  rw [recurrence4Scalar1Left_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (222 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (222 + x) *
        remainder4Coefficient1.coeff (222 - (222 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 222 + x
  · rw [recurrence4LeadingSquare_coeff_high (222 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (222 - (222 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_222 :
    recurrence4Scalar1Left.coeff 222 =
      (((((52281889225162533322107181 * 10 ^ 70 +
        1271765626178948416587147704991530700591663404512220683262542935236595) * 10 ^ 70 +
        9740316414767108584239866627102477910935688397285682243607291540332132) * 10 ^ 70 +
        3034644495780990685166949811371742632860493371551710451105211146392335) * 10 ^ 70 +
        7724347502972492890627357921679285813699165152566550612646912723898910) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (222 - x)) = _
  rw [show 223 = 32 +
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
  rw [recurrence4Scalar1Left_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (223 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (223 + x) *
        remainder4Coefficient1.coeff (223 - (223 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 223 + x
  · rw [recurrence4LeadingSquare_coeff_high (223 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (223 - (223 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_223 :
    recurrence4Scalar1Left.coeff 223 =
      -(((((77701471394438519022330296 * 10 ^ 70 +
        9568070133251412116935743286714049174307213785315974892751041063825495) * 10 ^ 70 +
        6123985748522948147758038507099875502141715955212039310639124225847208) * 10 ^ 70 +
        3208435315655486209386968506221609602471753687017091272948212588770450) * 10 ^ 70 +
        2493453206560877532126728563880748918305166258009838929249177191499002) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (223 - x)) = _
  rw [show 224 = 33 +
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
  rw [recurrence4Scalar1Left_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (224 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (224 + x) *
        remainder4Coefficient1.coeff (224 - (224 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 224 + x
  · rw [recurrence4LeadingSquare_coeff_high (224 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (224 - (224 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_224 :
    recurrence4Scalar1Left.coeff 224 =
      (((((113814408323352876220922275 * 10 ^ 70 +
        1426815712408759138377827873466865816468137668254805960627499583711597) * 10 ^ 70 +
        8477938135978653260495543164112605836166850598694213739785230317506642) * 10 ^ 70 +
        6140578594475549809298910020810762154696153952773909394696925368406945) * 10 ^ 70 +
        8770907485576819916601017963908247177804901086105896755863375087934426) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (224 - x)) = _
  rw [show 225 = 34 +
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
  rw [recurrence4Scalar1Left_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (225 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (225 + x) *
        remainder4Coefficient1.coeff (225 - (225 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 225 + x
  · rw [recurrence4LeadingSquare_coeff_high (225 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (225 - (225 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_225 :
    recurrence4Scalar1Left.coeff 225 =
      -(((((164296565878985349334917833 * 10 ^ 70 +
        2140824760232090463885041957832657006930192164748815904953313221651779) * 10 ^ 70 +
        4266774218216044649352031667947753913890183354514458421238300526759965) * 10 ^ 70 +
        6513181077299351346375269060735210290283962440196655043486012548609291) * 10 ^ 70 +
        9133019611988046161991922700860628886216649732844393855409198638586180) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (225 - x)) = _
  rw [show 226 = 35 +
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
  rw [recurrence4Scalar1Left_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (226 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (226 + x) *
        remainder4Coefficient1.coeff (226 - (226 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 226 + x
  · rw [recurrence4LeadingSquare_coeff_high (226 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (226 - (226 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_226 :
    recurrence4Scalar1Left.coeff 226 =
      (((((233718493325319791910666174 * 10 ^ 70 +
        5945835181686849177377279636956946990991179417881231905870620519731668) * 10 ^ 70 +
        0606039673642295825949429171581176167394162271926464648398113925411458) * 10 ^ 70 +
        5633962713857016616891185551017533626613808480417041611675323094616087) * 10 ^ 70 +
        2225249865279834595040061601059933385735899094453384318802621968940801) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (226 - x)) = _
  rw [show 227 = 36 +
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
  rw [recurrence4Scalar1Left_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (227 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (227 + x) *
        remainder4Coefficient1.coeff (227 - (227 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 227 + x
  · rw [recurrence4LeadingSquare_coeff_high (227 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (227 - (227 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_227 :
    recurrence4Scalar1Left.coeff 227 =
      -(((((327610405988392242444207521 * 10 ^ 70 +
        7282034802839993568628925596208934704501713830007168392852068195891185) * 10 ^ 70 +
        2318239453057531789536047310596772563872791489614418506658113749905351) * 10 ^ 70 +
        5048507420134853326400060312399188991592818644619588742385314600036458) * 10 ^ 70 +
        0076609386830602767579625689447244776795058064678513141554122719593980) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (227 - x)) = _
  rw [show 228 = 37 +
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
  rw [recurrence4Scalar1Left_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (228 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (228 + x) *
        remainder4Coefficient1.coeff (228 - (228 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 228 + x
  · rw [recurrence4LeadingSquare_coeff_high (228 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (228 - (228 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_228 :
    recurrence4Scalar1Left.coeff 228 =
      (((((452465143319850015249378481 * 10 ^ 70 +
        1944804039275560197445790167932946495119975287194243085419824794084904) * 10 ^ 70 +
        3818027068067285643482073895645243108451140641674871192115867621272184) * 10 ^ 70 +
        5946716250845643599463767067139486300857969923067054297291790921220879) * 10 ^ 70 +
        8168051624574349468327016200888422777923127206140917591535066390900697) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (228 - x)) = _
  rw [show 229 = 38 +
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
  rw [recurrence4Scalar1Left_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (229 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (229 + x) *
        remainder4Coefficient1.coeff (229 - (229 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 229 + x
  · rw [recurrence4LeadingSquare_coeff_high (229 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (229 - (229 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_229 :
    recurrence4Scalar1Left.coeff 229 =
      -(((((615649988072041095160893519 * 10 ^ 70 +
        2298630553434790607307188609055687054174364539608985663537758665003688) * 10 ^ 70 +
        2636857320557259679819669748498019428021689516055019772532359022853594) * 10 ^ 70 +
        7059611795744013689400312106468501576963371937327646161901996287036169) * 10 ^ 70 +
        4985635854491821149979834949860106287013805121560632275244637498204405) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (229 - x)) = _
  rw [show 230 = 39 +
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
  rw [recurrence4Scalar1Left_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (230 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (230 + x) *
        remainder4Coefficient1.coeff (230 - (230 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 230 + x
  · rw [recurrence4LeadingSquare_coeff_high (230 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (230 - (230 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_230 :
    recurrence4Scalar1Left.coeff 230 =
      (((((825196745919642999623075881 * 10 ^ 70 +
        3622712122492337005322415548214009177237060910987226974768010754193223) * 10 ^ 70 +
        7870877362313045958395373375388294614902018774829276524950666499405966) * 10 ^ 70 +
        0673247916042413998132737632215297800984039009077285221769523733366735) * 10 ^ 70 +
        6218620317648894172314366458754396769362470045575871432804790624214646) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (230 - x)) = _
  rw [show 231 = 40 +
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
  rw [recurrence4Scalar1Left_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (231 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (231 + x) *
        remainder4Coefficient1.coeff (231 - (231 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 231 + x
  · rw [recurrence4LeadingSquare_coeff_high (231 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (231 - (231 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_231 :
    recurrence4Scalar1Left.coeff 231 =
      -(((((1089441779005643657583358826 * 10 ^ 70 +
        4791490667458665178365563803432162027387291456716802537664483385236473) * 10 ^ 70 +
        9437190983624843721745081277190642737981659968759458513553385342833932) * 10 ^ 70 +
        1739909317478174054622858887692977600484535929698514128068955116156977) * 10 ^ 70 +
        7460228135682486322462346320352789544867571004229977179282610002290214) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (231 - x)) = _
  rw [show 232 = 41 +
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
  rw [recurrence4Scalar1Left_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (232 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (232 + x) *
        remainder4Coefficient1.coeff (232 - (232 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 232 + x
  · rw [recurrence4LeadingSquare_coeff_high (232 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (232 - (232 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_232 :
    recurrence4Scalar1Left.coeff 232 =
      (((((1416495056742011769223485138 * 10 ^ 70 +
        0811047386059668752435434114676612870517059339695882496434796754507172) * 10 ^ 70 +
        8244555470245424829364361229243697390226235293387018654236283614587332) * 10 ^ 70 +
        5655932123268509964372857877536406816686977132172813720789809809453903) * 10 ^ 70 +
        8969279911757291242196029038082346847771333368987671847780090177737935) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (232 - x)) = _
  rw [show 233 = 42 +
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
  rw [recurrence4Scalar1Left_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (233 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (233 + x) *
        remainder4Coefficient1.coeff (233 - (233 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 233 + x
  · rw [recurrence4LeadingSquare_coeff_high (233 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (233 - (233 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_233 :
    recurrence4Scalar1Left.coeff 233 =
      -(((((1813530693773275660649375296 * 10 ^ 70 +
        5110132482015974360656063900846990348037129786511075188565234227889600) * 10 ^ 70 +
        4254443303718444922175179396056084089374750233522082813308775748199991) * 10 ^ 70 +
        0364576553552449457139534147684884025814456955355484044323572632456251) * 10 ^ 70 +
        0277257974777517926502570306440344159731336868887886850078091613429242) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (233 - x)) = _
  rw [show 234 = 43 +
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
  rw [recurrence4Scalar1Left_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (234 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (234 + x) *
        remainder4Coefficient1.coeff (234 - (234 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 234 + x
  · rw [recurrence4LeadingSquare_coeff_high (234 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (234 - (234 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_234 :
    recurrence4Scalar1Left.coeff 234 =
      (((((2285911190137228061560453745 * 10 ^ 70 +
        8265005363448339152013600763037790627007685517101197986237908187836319) * 10 ^ 70 +
        2684112026651209276729042845179916994357099184075144312595184067389498) * 10 ^ 70 +
        0743503754252896237405020683298572491508830730147741557878206432889770) * 10 ^ 70 +
        5256180989873979480405692234220104230138399500137260228522626899209503) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (234 - x)) = _
  rw [show 235 = 44 +
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
  rw [recurrence4Scalar1Left_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (235 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (235 + x) *
        remainder4Coefficient1.coeff (235 - (235 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 235 + x
  · rw [recurrence4LeadingSquare_coeff_high (235 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (235 - (235 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_235 :
    recurrence4Scalar1Left.coeff 235 =
      -(((((2836182990614060718226541039 * 10 ^ 70 +
        7441530584930820177296184435022248240580792606189885936942699827113105) * 10 ^ 70 +
        1416899202128441541190283923628848988722700561844034491705582412104584) * 10 ^ 70 +
        5750439070525419995029140567795726329917443518100951280567114520005418) * 10 ^ 70 +
        3354365920775600609542510041663303027840905476631360656423417120983101) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (235 - x)) = _
  rw [show 236 = 45 +
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
  rw [recurrence4Scalar1Left_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (236 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (236 + x) *
        remainder4Coefficient1.coeff (236 - (236 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 236 + x
  · rw [recurrence4LeadingSquare_coeff_high (236 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (236 - (236 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_236 :
    recurrence4Scalar1Left.coeff 236 =
      (((((3463010121751328725429549920 * 10 ^ 70 +
        1046175160846593467461122025550807035324074124011990870469329429172944) * 10 ^ 70 +
        4612709475438698367077539513594959589480319788557090687240867376433051) * 10 ^ 70 +
        6337616966173220089849486174145464753242855955374311202692966310564717) * 10 ^ 70 +
        4639219422009474789049924351127536417992213492645028948080614295882148) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (236 - x)) = _
  rw [show 237 = 46 +
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
  rw [recurrence4Scalar1Left_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (237 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (237 + x) *
        remainder4Coefficient1.coeff (237 - (237 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 237 + x
  · rw [recurrence4LeadingSquare_coeff_high (237 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (237 - (237 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_237 :
    recurrence4Scalar1Left.coeff 237 =
      -(((((4160142296704420700436302216 * 10 ^ 70 +
        1049020991258936056306691772672880285640667476491314985941790237609623) * 10 ^ 70 +
        7063604877620116762031030731760773886418298427398887045861589851202290) * 10 ^ 70 +
        7726828345997819202117563385934668096919744848625477681905775278932643) * 10 ^ 70 +
        0152959130266612848187336191664731610641344363362927689265779629536192) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (237 - x)) = _
  rw [show 238 = 47 +
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
  rw [recurrence4Scalar1Left_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (238 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (238 + x) *
        remainder4Coefficient1.coeff (238 - (238 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 238 + x
  · rw [recurrence4LeadingSquare_coeff_high (238 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (238 - (238 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_238 :
    recurrence4Scalar1Left.coeff 238 =
      (((((4915539556003682748898280443 * 10 ^ 70 +
        3382822868322110011194509250435099926959735044099523689496683152486001) * 10 ^ 70 +
        0813847558372354287251708586465451996683705134246825534808167575735999) * 10 ^ 70 +
        8602635088732793385448644421716537871121395007754055140862609175713830) * 10 ^ 70 +
        4452595489129709267680652467351833321969487699326601595489531624114623) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (238 - x)) = _
  rw [show 239 = 48 +
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
  rw [recurrence4Scalar1Left_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (239 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (239 + x) *
        remainder4Coefficient1.coeff (239 - (239 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 239 + x
  · rw [recurrence4LeadingSquare_coeff_high (239 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (239 - (239 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_239 :
    recurrence4Scalar1Left.coeff 239 =
      -(((((5710792023110972301926956388 * 10 ^ 70 +
        4190955707126695088400525328718611727643687882009627006189551468596270) * 10 ^ 70 +
        5598145003418292580422325890405943187617620960165784442309610020474170) * 10 ^ 70 +
        5722697261459094071616169338636434828122989640717274043898601039008565) * 10 ^ 70 +
        2458868301073747629683082675231499218782747582918329758534948906415621) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (239 - x)) = _
  rw [show 240 = 49 +
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
  rw [recurrence4Scalar1Left_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (240 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (240 + x) *
        remainder4Coefficient1.coeff (240 - (240 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 240 + x
  · rw [recurrence4LeadingSquare_coeff_high (240 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (240 - (240 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_240 :
    recurrence4Scalar1Left.coeff 240 =
      (((((6520975431002850371197773121 * 10 ^ 70 +
        5152466622145623911680743215769139851694501373813905910151603520911131) * 10 ^ 70 +
        9709816968725286353892455442166405156940002101117144097977005492782279) * 10 ^ 70 +
        0376012413736225465085331780206415773425493639332432018644122772390240) * 10 ^ 70 +
        8208668653351851719418204506351840497121418487248055446246084842950181) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (240 - x)) = _
  rw [show 241 = 50 +
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
  rw [recurrence4Scalar1Left_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (241 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (241 + x) *
        remainder4Coefficient1.coeff (241 - (241 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 241 + x
  · rw [recurrence4LeadingSquare_coeff_high (241 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (241 - (241 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_241 :
    recurrence4Scalar1Left.coeff 241 =
      -(((((7315066350757307238836761801 * 10 ^ 70 +
        9520432064651420990216227187877301256750126444690806369060045987295272) * 10 ^ 70 +
        0804578034463668561109427654360839384641113531075458495948576443108081) * 10 ^ 70 +
        5609589461263355097736630664851348805158420920362049395846324097424424) * 10 ^ 70 +
        9307878859623156869202621793775566323723227638915220588123965625635385) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (241 - x)) = _
  rw [show 242 = 51 +
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
  rw [recurrence4Scalar1Left_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (242 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (242 + x) *
        remainder4Coefficient1.coeff (242 - (242 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 242 + x
  · rw [recurrence4LeadingSquare_coeff_high (242 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (242 - (242 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_242 :
    recurrence4Scalar1Left.coeff 242 =
      (((((8057003103471475965886868913 * 10 ^ 70 +
        5976437449778574804965896832893105661807611207013135660918024977041750) * 10 ^ 70 +
        8862218096582763430660778137786944762309749226190347944273931419695444) * 10 ^ 70 +
        7244607120744610674270789849492517473526525358979771965198332893662140) * 10 ^ 70 +
        8296088544129503045680165608816047057671049623106476743151163457036817) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (242 - x)) = _
  rw [show 243 = 52 +
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
  rw [recurrence4Scalar1Left_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (243 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (243 + x) *
        remainder4Coefficient1.coeff (243 - (243 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 243 + x
  · rw [recurrence4LeadingSquare_coeff_high (243 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (243 - (243 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_243 :
    recurrence4Scalar1Left.coeff 243 =
      -(((((8707419647379254952476228598 * 10 ^ 70 +
        6055176852181496251306803225538808550778042528877593429682292652015620) * 10 ^ 70 +
        8565790765322754625370951729703861087558191391327138248189766133225712) * 10 ^ 70 +
        6769272430941415414630843943964480020377177816421182293301162059134687) * 10 ^ 70 +
        1222155995763456327056500739622438091419207128530133057694182480853522) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (243 - x)) = _
  rw [show 244 = 53 +
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
  rw [recurrence4Scalar1Left_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (244 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (244 + x) *
        remainder4Coefficient1.coeff (244 - (244 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 244 + x
  · rw [recurrence4LeadingSquare_coeff_high (244 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (244 - (244 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_244 :
    recurrence4Scalar1Left.coeff 244 =
      (((((9226004334886739480551615663 * 10 ^ 70 +
        2591422393211508703151598977691016586349618323731918226312267463592628) * 10 ^ 70 +
        1853079963547392562685114654348064849306825465027512111744280087643247) * 10 ^ 70 +
        3388121557085089083281946671391066671359057759095161716271414646870815) * 10 ^ 70 +
        3179740275310278145024770375412330167354117666193074058059273419833055) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (244 - x)) = _
  rw [show 245 = 54 +
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
  rw [recurrence4Scalar1Left_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (245 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (245 + x) *
        remainder4Coefficient1.coeff (245 - (245 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 245 + x
  · rw [recurrence4LeadingSquare_coeff_high (245 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (245 - (245 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_245 :
    recurrence4Scalar1Left.coeff 245 =
      -(((((9574351018572074293520434948 * 10 ^ 70 +
        9009594936515919696745964565798199974258571250809430544371686079968999) * 10 ^ 70 +
        5412020340300650703865976418134874651261816738442010849879964824274492) * 10 ^ 70 +
        9651677467128303060612201502296738850118156095437807093713594148977516) * 10 ^ 70 +
        5777458722668769561936724491846409679732588808865015042011337694587941) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (245 - x)) = _
  rw [show 246 = 55 +
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
  rw [recurrence4Scalar1Left_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (246 + x) *
        remainder4Coefficient1.coeff (246 - (246 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 246 + x
  · rw [recurrence4LeadingSquare_coeff_high (246 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (246 - (246 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_246 :
    recurrence4Scalar1Left.coeff 246 =
      (((((9719087326442950558228533302 * 10 ^ 70 +
        6589787323404326136174104684876222348361504102973813862242731138698878) * 10 ^ 70 +
        6406744565314147301648071654116580419039059883077068286747754522934568) * 10 ^ 70 +
        0073440188579454672369972597801907755895750374249058299762624644626311) * 10 ^ 70 +
        6124070852169662929664389758038934925096829825471931339347963183492091) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (246 - x)) = _
  rw [show 247 = 56 +
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
  rw [recurrence4Scalar1Left_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (247 + x) *
        remainder4Coefficient1.coeff (247 - (247 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 247 + x
  · rw [recurrence4LeadingSquare_coeff_high (247 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (247 - (247 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_247 :
    recurrence4Scalar1Left.coeff 247 =
      -(((((9634996602866077532714534660 * 10 ^ 70 +
        5267139533126966537071205425565210125338713335201857264473390840153406) * 10 ^ 70 +
        3947258355707970722553833745279543310379194606758828844910486504204509) * 10 ^ 70 +
        2537591840077230145926626938760525444848151553999748978980194490049687) * 10 ^ 70 +
        5921259785127590234363481617480024540768725994661013837337872654698236) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (247 - x)) = _
  rw [show 248 = 57 +
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
  rw [recurrence4Scalar1Left_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (248 + x) *
        remainder4Coefficient1.coeff (248 - (248 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 248 + x
  · rw [recurrence4LeadingSquare_coeff_high (248 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (248 - (248 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_248 :
    recurrence4Scalar1Left.coeff 248 =
      (((((9307808523144226131515577154 * 10 ^ 70 +
        5649505778907938966863767559715810252804382302350006580557633994119747) * 10 ^ 70 +
        4788417554644314355913921366891431295022429697580589478765437872318802) * 10 ^ 70 +
        6077450539152915596181664486747945860961781795746988423378863475037541) * 10 ^ 70 +
        6175256397872287130290747603121194918542443809453781657921229577690897) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (248 - x)) = _
  rw [show 249 = 58 +
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
  rw [recurrence4Scalar1Left_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (249 + x) *
        remainder4Coefficient1.coeff (249 - (249 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 249 + x
  · rw [recurrence4LeadingSquare_coeff_high (249 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (249 - (249 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_249 :
    recurrence4Scalar1Left.coeff 249 =
      -(((((8736328953892618777356563721 * 10 ^ 70 +
        6238067337036506735869655601997002704221793711856729689923390040753833) * 10 ^ 70 +
        9869915958972138952715096722383629872556099846010259513268001999333415) * 10 ^ 70 +
        2014462718243004656945838747135230658830569191223119901922548682371696) * 10 ^ 70 +
        4442055081350312107873035716044065547610304266431845215928467591671815) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (249 - x)) = _
  rw [show 250 = 59 +
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
  rw [recurrence4Scalar1Left_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (250 + x) *
        remainder4Coefficient1.coeff (250 - (250 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 250 + x
  · rw [recurrence4LeadingSquare_coeff_high (250 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (250 - (250 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_250 :
    recurrence4Scalar1Left.coeff 250 =
      (((((7933618040210027699333668721 * 10 ^ 70 +
        8075522651564127238691989941150947544634790731622267609810271649476933) * 10 ^ 70 +
        5888271902283696182590603865398115427554757641460525321802733955320291) * 10 ^ 70 +
        3783532743854801477892580926417117377193617649333217592558715127834294) * 10 ^ 70 +
        8685082008183215517963885405733570262822629643840292816511611556139083) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (250 - x)) = _
  rw [show 251 = 60 +
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
  rw [recurrence4Scalar1Left_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (251 + x) *
        remainder4Coefficient1.coeff (251 - (251 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 251 + x
  · rw [recurrence4LeadingSquare_coeff_high (251 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (251 - (251 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_251 :
    recurrence4Scalar1Left.coeff 251 =
      -(((((6927006485844067499077555738 * 10 ^ 70 +
        3670945552187489121940778102263477564976756254139092009141412864456664) * 10 ^ 70 +
        0420404113153994001056989456326612771546264012553258124969360402897009) * 10 ^ 70 +
        9494038003476360264967765597739000960269252044042225576620842032155457) * 10 ^ 70 +
        6871271939208836707408937439899117360304388515146549402097480131965411) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (251 - x)) = _
  rw [show 252 = 61 +
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
  rw [recurrence4Scalar1Left_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (252 + x) *
        remainder4Coefficient1.coeff (252 - (252 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 252 + x
  · rw [recurrence4LeadingSquare_coeff_high (252 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (252 - (252 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_252 :
    recurrence4Scalar1Left.coeff 252 =
      (((((5756856498159478080310862742 * 10 ^ 70 +
        7543541759099436637558456954522754928570442619928716839395544838265599) * 10 ^ 70 +
        1831498224524220623973394741889907765667399326156810641418164004610012) * 10 ^ 70 +
        7118430165560821796071418712602298929336812187700675270908479478373810) * 10 ^ 70 +
        5532200792004812209801897812391702411345497723221724927848214880682640) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (252 - x)) = _
  rw [show 253 = 62 +
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
  rw [recurrence4Scalar1Left_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (253 + x) *
        remainder4Coefficient1.coeff (253 - (253 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 253 + x
  · rw [recurrence4LeadingSquare_coeff_high (253 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (253 - (253 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_253 :
    recurrence4Scalar1Left.coeff 253 =
      -(((((4474112496266397701996713678 * 10 ^ 70 +
        7791851918717842417967037380516367078945702608541309905981271114664692) * 10 ^ 70 +
        4188337643880820721714110707532663775704785332377292097845113883204251) * 10 ^ 70 +
        7629322432835036552469547508267233329990333515422570781035389170927942) * 10 ^ 70 +
        9318841293043741356878377871701766869706583508875269631891364243233960) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (253 - x)) = _
  rw [show 254 = 63 +
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
  rw [recurrence4Scalar1Left_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (254 + x) *
        remainder4Coefficient1.coeff (254 - (254 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 254 + x
  · rw [recurrence4LeadingSquare_coeff_high (254 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (254 - (254 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_254 :
    recurrence4Scalar1Left.coeff 254 =
      (((((3136829348427769520657254701 * 10 ^ 70 +
        7460575219655912961616723825361012260932794612945604315403069803552592) * 10 ^ 70 +
        4000971698506462063741499823976873838835871876767857073925502622052110) * 10 ^ 70 +
        1704720678103511573318156467561193201297766971715726276103419373178223) * 10 ^ 70 +
        2384326379296277133908233965086663967125385218475821362851819600920291) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (254 - x)) = _
  rw [show 255 = 64 +
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
  rw [recurrence4Scalar1Left_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (255 + x) *
        remainder4Coefficient1.coeff (255 - (255 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 255 + x
  · rw [recurrence4LeadingSquare_coeff_high (255 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (255 - (255 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_255 :
    recurrence4Scalar1Left.coeff 255 =
      -(((((1805992531907459880646408051 * 10 ^ 70 +
        1378541113181113314919039266947942816439793584770143362912270130442441) * 10 ^ 70 +
        7083732299116445151882022038896417151858713134033689678425853209224773) * 10 ^ 70 +
        6401799438134711786131943436201348417308812113381400922135084274610977) * 10 ^ 70 +
        8412276650537283713296875293453105130217786008900490910725836196561184) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (255 - x)) = _
  rw [show 256 = 65 +
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
  rw [recurrence4Scalar1Left_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (256 + x) *
        remainder4Coefficient1.coeff (256 - (256 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 256 + x
  · rw [recurrence4LeadingSquare_coeff_high (256 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (256 - (256 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_256 :
    recurrence4Scalar1Left.coeff 256 =
      (((((541036366578576034310583309 * 10 ^ 70 +
        4925297556997894761055432049545984899600671106977482222303573856187130) * 10 ^ 70 +
        2666649359237018319381423465444736422222579577276223210266072600905183) * 10 ^ 70 +
        4684422495571062950007179796693163313355295936893253321557089878688233) * 10 ^ 70 +
        8283114609679712699955257554309051774291071548489586547313464668157775) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (256 - x)) = _
  rw [show 257 = 66 +
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
  rw [recurrence4Scalar1Left_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (257 + x) *
        remainder4Coefficient1.coeff (257 - (257 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 257 + x
  · rw [recurrence4LeadingSquare_coeff_high (257 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (257 - (257 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_257 :
    recurrence4Scalar1Left.coeff 257 =
      (((((604490970864071608605352423 * 10 ^ 70 +
        5118704746486471947459957353477318600488786137540121650394066271915943) * 10 ^ 70 +
        6805431984186432270781622063686058041216584751171092081748523203267665) * 10 ^ 70 +
        7886925217983304624860430276261296561925900522472732799098993538797808) * 10 ^ 70 +
        9799634438398554895966590872567988917240021886119264525318004229901371) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (257 - x)) = _
  rw [show 258 = 67 +
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
  rw [recurrence4Scalar1Left_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (258 + x) *
        remainder4Coefficient1.coeff (258 - (258 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 258 + x
  · rw [recurrence4LeadingSquare_coeff_high (258 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (258 - (258 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_258 :
    recurrence4Scalar1Left.coeff 258 =
      -(((((1586680836797053520714582298 * 10 ^ 70 +
        1181771622422485648467312444203179605178675087520037272664099903480924) * 10 ^ 70 +
        6513330748328245425679444428575843575593921597357443526169361584997080) * 10 ^ 70 +
        7596402529393918124462238391473073870190180187636260612059908008326388) * 10 ^ 70 +
        9287632713379171453637695518743939904439839035432398509736452192998713) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (258 - x)) = _
  rw [show 259 = 68 +
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
  rw [recurrence4Scalar1Left_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (259 + x) *
        remainder4Coefficient1.coeff (259 - (259 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 259 + x
  · rw [recurrence4LeadingSquare_coeff_high (259 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (259 - (259 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_259 :
    recurrence4Scalar1Left.coeff 259 =
      (((((2374070175360243059399651697 * 10 ^ 70 +
        1223868900887043581883110307086785931313785772241191578689209206811929) * 10 ^ 70 +
        9828421757374502821979276929319939208230953965472172467824740021059190) * 10 ^ 70 +
        7504460624568642565908757768401636126573335047635678034364843291257111) * 10 ^ 70 +
        0225517292201114885826160022261180745006244178278691285004332593595950) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (259 - x)) = _
  rw [show 260 = 69 +
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
  rw [recurrence4Scalar1Left_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (260 + x) *
        remainder4Coefficient1.coeff (260 - (260 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 260 + x
  · rw [recurrence4LeadingSquare_coeff_high (260 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (260 - (260 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_260 :
    recurrence4Scalar1Left.coeff 260 =
      -(((((2949249059872805588854129842 * 10 ^ 70 +
        1922338246337094916945350284852356916797634701209351346911592014455409) * 10 ^ 70 +
        1814964674181483434247470213909425619137384395529126602890756998144180) * 10 ^ 70 +
        4495431946067174211675041431879166360956119946029549326079200672736364) * 10 ^ 70 +
        9655670284996585047745891237283281518036400734253940764226561011736007) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (260 - x)) = _
  rw [show 261 = 70 +
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
  rw [recurrence4Scalar1Left_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (261 + x) *
        remainder4Coefficient1.coeff (261 - (261 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 261 + x
  · rw [recurrence4LeadingSquare_coeff_high (261 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (261 - (261 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_261 :
    recurrence4Scalar1Left.coeff 261 =
      (((((3309162028234923841189522528 * 10 ^ 70 +
        5495066075840522302971643728961779269496999275555087009959625999882305) * 10 ^ 70 +
        3461832015689901105224031396650670800039133859210835576795921495450653) * 10 ^ 70 +
        4917634941172765224169622141419756175822614122977866396049025229402171) * 10 ^ 70 +
        8056583828493648659440119790565116107981355636251570020540819233276045) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (261 - x)) = _
  rw [show 262 = 71 +
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
  rw [recurrence4Scalar1Left_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (262 + x) *
        remainder4Coefficient1.coeff (262 - (262 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 262 + x
  · rw [recurrence4LeadingSquare_coeff_high (262 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (262 - (262 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_262 :
    recurrence4Scalar1Left.coeff 262 =
      -(((((3464147294611502928550534691 * 10 ^ 70 +
        3212038989379478256823539323597946177001021441801013891470305649510576) * 10 ^ 70 +
        4140976021295187694392710453732732113896779730186852058548848031311982) * 10 ^ 70 +
        9644196543065535604596096403092772991152786890214837026228093087959733) * 10 ^ 70 +
        5900641183320379131521043156824832917555416929777164271848024258370112) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (262 - x)) = _
  rw [show 263 = 72 +
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
  rw [recurrence4Scalar1Left_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (263 + x) *
        remainder4Coefficient1.coeff (263 - (263 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 263 + x
  · rw [recurrence4LeadingSquare_coeff_high (263 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (263 - (263 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_263 :
    recurrence4Scalar1Left.coeff 263 =
      (((((3435896743722092576699822692 * 10 ^ 70 +
        4874381345018449957159769298514501139722413345980655689126030248640244) * 10 ^ 70 +
        6322435710161061148260724982420658380148550617997558728936658147546323) * 10 ^ 70 +
        2804878761260167395599789854066531232216143074631042717653148049925777) * 10 ^ 70 +
        1574605642781189900389196917047833706690671839445864016767646107706412) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (263 - x)) = _
  rw [show 264 = 73 +
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
  rw [recurrence4Scalar1Left_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (264 + x) *
        remainder4Coefficient1.coeff (264 - (264 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 264 + x
  · rw [recurrence4LeadingSquare_coeff_high (264 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (264 - (264 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_264 :
    recurrence4Scalar1Left.coeff 264 =
      -(((((3254627119080472140953501394 * 10 ^ 70 +
        6835263084512342073791449499003023786048822707107209629564331611800638) * 10 ^ 70 +
        0065935875862900435352040498243550979177891398717327320195731272192281) * 10 ^ 70 +
        8332011526277798634416213453130963242960982944770731446665148860686167) * 10 ^ 70 +
        8074978489818245937707110212787300416804235543868339091963826364100891) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (264 - x)) = _
  rw [show 265 = 74 +
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
  rw [recurrence4Scalar1Left_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (265 + x) *
        remainder4Coefficient1.coeff (265 - (265 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 265 + x
  · rw [recurrence4LeadingSquare_coeff_high (265 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (265 - (265 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_265 :
    recurrence4Scalar1Left.coeff 265 =
      (((((2955816345700090159822779913 * 10 ^ 70 +
        9323463551720500986780480543344711373153425037542952090977903866309391) * 10 ^ 70 +
        8502463321585417432925038575629364783295618190263312874390580418289622) * 10 ^ 70 +
        9742162592146316325312714203927760934785674367748335702448993352251615) * 10 ^ 70 +
        3914199659862565434742793855418746087617410041391643314435255408377914) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (265 - x)) = _
  rw [show 266 = 75 +
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
  rw [recurrence4Scalar1Left_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (266 + x) *
        remainder4Coefficient1.coeff (266 - (266 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 266 + x
  · rw [recurrence4LeadingSquare_coeff_high (266 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (266 - (266 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_266 :
    recurrence4Scalar1Left.coeff 266 =
      -(((((2576873232289360510631625789 * 10 ^ 70 +
        7964430774688375858116968248778220997238544105727288286132663059779535) * 10 ^ 70 +
        8617820164626329222441504276030776168998712188922849586408408026299282) * 10 ^ 70 +
        7193398376715435018032947623385200473027485730277242620586810675000138) * 10 ^ 70 +
        6332624753984012204004501977512870755520943495288566336898590905426579) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (266 - x)) = _
  rw [show 267 = 76 +
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
  rw [recurrence4Scalar1Left_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (267 + x) *
        remainder4Coefficient1.coeff (267 - (267 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 267 + x
  · rw [recurrence4LeadingSquare_coeff_high (267 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (267 - (267 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_267 :
    recurrence4Scalar1Left.coeff 267 =
      (((((2154076342018371345042222019 * 10 ^ 70 +
        6526783476919404825749304446591595145323419183336420620808581632068033) * 10 ^ 70 +
        1809275756767208563992825875007513365047890095346040617055586772947330) * 10 ^ 70 +
        9432781046244196997108075980661907051086645296816098049749159923903028) * 10 ^ 70 +
        5371257929221378132996534696267629939521220561769716949345163288689228) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (267 - x)) = _
  rw [show 268 = 77 +
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
  rw [recurrence4Scalar1Left_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (268 + x) *
        remainder4Coefficient1.coeff (268 - (268 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 268 + x
  · rw [recurrence4LeadingSquare_coeff_high (268 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (268 - (268 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_268 :
    recurrence4Scalar1Left.coeff 268 =
      -(((((1720047734557428837083072656 * 10 ^ 70 +
        9830981548104226022505837348132070650130019696009235002753420329900172) * 10 ^ 70 +
        9784547553267853538184181221228080411869315560716825042856700850379194) * 10 ^ 70 +
        5427825224353713519208717944330109215853213200461879653305109559821361) * 10 ^ 70 +
        1998328271444855841707090843592475765755871657520988808771480595363404) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (268 - x)) = _
  rw [show 269 = 78 +
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
  rw [recurrence4Scalar1Left_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (269 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (269 + x) *
        remainder4Coefficient1.coeff (269 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 269 + x
  · rw [recurrence4LeadingSquare_coeff_high (269 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (269 - (269 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_269 :
    recurrence4Scalar1Left.coeff 269 =
      (((((1301933263640915454046416562 * 10 ^ 70 +
        1047765517288697629922192428361121009171910745415604408111396462056079) * 10 ^ 70 +
        1650049774484133381600892861410014899407282923006876974869457869387360) * 10 ^ 70 +
        6730468170955694546646052992320668255169034566112229168654302315383417) * 10 ^ 70 +
        6045311848026358311869646845904133507688561111154883678175115199845418) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (269 - x)) = _
  rw [show 270 = 79 +
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
  rw [recurrence4Scalar1Left_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (270 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (270 + x) *
        remainder4Coefficient1.coeff (270 - (270 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 270 + x
  · rw [recurrence4LeadingSquare_coeff_high (270 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (270 - (270 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_270 :
    recurrence4Scalar1Left.coeff 270 =
      -(((((920358764350887398259341869 * 10 ^ 70 +
        5063340318057849730090473893284667107205107962256002815983684742864199) * 10 ^ 70 +
        1587710836110412952142533190566810286516054200790266650205383145158984) * 10 ^ 70 +
        4309923243996374311601742843224472833495944163407112403674152994229249) * 10 ^ 70 +
        9712774156468948091606606211657018095719445920626592571381410684473132) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (270 - x)) = _
  rw [show 271 = 80 +
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
  rw [recurrence4Scalar1Left_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A1_coeff_high (271 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar1Left_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (271 + x) *
        remainder4Coefficient1.coeff (271 - (271 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 271 + x
  · rw [recurrence4LeadingSquare_coeff_high (271 + x) hleft]
    norm_num
  · rw [recurrence4A1_coeff_low
      (271 - (271 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar1Left_coeff_271 :
    recurrence4Scalar1Left.coeff 271 =
      (((((589135595178670083182027202 * 10 ^ 70 +
        6732462447171459339575856492477783970101177568330814336564975926662045) * 10 ^ 70 +
        8999398474510218759175567444756595095746123673145659372678521274616432) * 10 ^ 70 +
        7424100551177898165927566746125474827138892748727656463330358450024849) * 10 ^ 70 +
        1918321316201057021928986953950284358376585381012710213029816198900085) : ℚ) := by
  unfold recurrence4Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient1.coeff (271 - x)) = _
  rw [show 272 = 81 +
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
  rw [recurrence4Scalar1Left_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1Left_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
