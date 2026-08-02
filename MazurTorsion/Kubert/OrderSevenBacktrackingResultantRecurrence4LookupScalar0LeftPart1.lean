/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4A0_coeff_1
  recurrence4A0_coeff_10
  recurrence4A0_coeff_100
  recurrence4A0_coeff_101
  recurrence4A0_coeff_102
  recurrence4A0_coeff_103
  recurrence4A0_coeff_104
  recurrence4A0_coeff_105
  recurrence4A0_coeff_106
  recurrence4A0_coeff_107
  recurrence4A0_coeff_108
  recurrence4A0_coeff_109
  recurrence4A0_coeff_11
  recurrence4A0_coeff_110
  recurrence4A0_coeff_111
  recurrence4A0_coeff_112
  recurrence4A0_coeff_113
  recurrence4A0_coeff_114
  recurrence4A0_coeff_115
  recurrence4A0_coeff_116
  recurrence4A0_coeff_117
  recurrence4A0_coeff_118
  recurrence4A0_coeff_119
  recurrence4A0_coeff_12
  recurrence4A0_coeff_120
  recurrence4A0_coeff_121
  recurrence4A0_coeff_122
  recurrence4A0_coeff_123
  recurrence4A0_coeff_124
  recurrence4A0_coeff_125
  recurrence4A0_coeff_126
  recurrence4A0_coeff_127
  recurrence4A0_coeff_128
  recurrence4A0_coeff_129
  recurrence4A0_coeff_13
  recurrence4A0_coeff_130
  recurrence4A0_coeff_131
  recurrence4A0_coeff_132
  recurrence4A0_coeff_133
  recurrence4A0_coeff_134
  recurrence4A0_coeff_135
  recurrence4A0_coeff_136
  recurrence4A0_coeff_137
  recurrence4A0_coeff_138
  recurrence4A0_coeff_139
  recurrence4A0_coeff_14
  recurrence4A0_coeff_140
  recurrence4A0_coeff_141
  recurrence4A0_coeff_142
  recurrence4A0_coeff_143
  recurrence4A0_coeff_144
  recurrence4A0_coeff_145
  recurrence4A0_coeff_146
  recurrence4A0_coeff_147
  recurrence4A0_coeff_148
  recurrence4A0_coeff_149
  recurrence4A0_coeff_15
  recurrence4A0_coeff_150
  recurrence4A0_coeff_151
  recurrence4A0_coeff_152
  recurrence4A0_coeff_153
  recurrence4A0_coeff_154
  recurrence4A0_coeff_155
  recurrence4A0_coeff_156

attribute [local simp]
  recurrence4A0_coeff_157
  recurrence4A0_coeff_158
  recurrence4A0_coeff_159
  recurrence4A0_coeff_16
  recurrence4A0_coeff_160
  recurrence4A0_coeff_161
  recurrence4A0_coeff_162
  recurrence4A0_coeff_163
  recurrence4A0_coeff_164
  recurrence4A0_coeff_165
  recurrence4A0_coeff_166
  recurrence4A0_coeff_167
  recurrence4A0_coeff_168
  recurrence4A0_coeff_169
  recurrence4A0_coeff_17
  recurrence4A0_coeff_170
  recurrence4A0_coeff_171
  recurrence4A0_coeff_172
  recurrence4A0_coeff_173
  recurrence4A0_coeff_174
  recurrence4A0_coeff_175
  recurrence4A0_coeff_176
  recurrence4A0_coeff_177
  recurrence4A0_coeff_178
  recurrence4A0_coeff_179
  recurrence4A0_coeff_18
  recurrence4A0_coeff_180
  recurrence4A0_coeff_181
  recurrence4A0_coeff_182
  recurrence4A0_coeff_183
  recurrence4A0_coeff_184
  recurrence4A0_coeff_185
  recurrence4A0_coeff_186
  recurrence4A0_coeff_187
  recurrence4A0_coeff_188
  recurrence4A0_coeff_189
  recurrence4A0_coeff_19
  recurrence4A0_coeff_190
  recurrence4A0_coeff_191
  recurrence4A0_coeff_192
  recurrence4A0_coeff_193
  recurrence4A0_coeff_194
  recurrence4A0_coeff_2
  recurrence4A0_coeff_20
  recurrence4A0_coeff_21
  recurrence4A0_coeff_22
  recurrence4A0_coeff_23
  recurrence4A0_coeff_24
  recurrence4A0_coeff_25
  recurrence4A0_coeff_26
  recurrence4A0_coeff_27
  recurrence4A0_coeff_28
  recurrence4A0_coeff_29
  recurrence4A0_coeff_3
  recurrence4A0_coeff_30
  recurrence4A0_coeff_31
  recurrence4A0_coeff_32
  recurrence4A0_coeff_33
  recurrence4A0_coeff_34
  recurrence4A0_coeff_35
  recurrence4A0_coeff_36
  recurrence4A0_coeff_37
  recurrence4A0_coeff_38
  recurrence4A0_coeff_39

attribute [local simp]
  recurrence4A0_coeff_4
  recurrence4A0_coeff_40
  recurrence4A0_coeff_41
  recurrence4A0_coeff_42
  recurrence4A0_coeff_43
  recurrence4A0_coeff_44
  recurrence4A0_coeff_45
  recurrence4A0_coeff_46
  recurrence4A0_coeff_47
  recurrence4A0_coeff_48
  recurrence4A0_coeff_49
  recurrence4A0_coeff_5
  recurrence4A0_coeff_50
  recurrence4A0_coeff_51
  recurrence4A0_coeff_52
  recurrence4A0_coeff_53
  recurrence4A0_coeff_54
  recurrence4A0_coeff_55
  recurrence4A0_coeff_56
  recurrence4A0_coeff_57
  recurrence4A0_coeff_58
  recurrence4A0_coeff_59
  recurrence4A0_coeff_6
  recurrence4A0_coeff_60
  recurrence4A0_coeff_61
  recurrence4A0_coeff_62
  recurrence4A0_coeff_63
  recurrence4A0_coeff_64
  recurrence4A0_coeff_65
  recurrence4A0_coeff_66
  recurrence4A0_coeff_67
  recurrence4A0_coeff_68
  recurrence4A0_coeff_69
  recurrence4A0_coeff_7
  recurrence4A0_coeff_70
  recurrence4A0_coeff_71
  recurrence4A0_coeff_72
  recurrence4A0_coeff_73
  recurrence4A0_coeff_74
  recurrence4A0_coeff_75
  recurrence4A0_coeff_76
  recurrence4A0_coeff_77
  recurrence4A0_coeff_78
  recurrence4A0_coeff_79
  recurrence4A0_coeff_8
  recurrence4A0_coeff_80
  recurrence4A0_coeff_81
  recurrence4A0_coeff_82
  recurrence4A0_coeff_83
  recurrence4A0_coeff_84
  recurrence4A0_coeff_85
  recurrence4A0_coeff_86
  recurrence4A0_coeff_87
  recurrence4A0_coeff_88
  recurrence4A0_coeff_89
  recurrence4A0_coeff_9
  recurrence4A0_coeff_90
  recurrence4A0_coeff_91
  recurrence4A0_coeff_92
  recurrence4A0_coeff_93
  recurrence4A0_coeff_94
  recurrence4A0_coeff_95
  recurrence4A0_coeff_96
  recurrence4A0_coeff_97

attribute [local simp]
  recurrence4A0_coeff_98
  recurrence4A0_coeff_99
  recurrence4LeadingSquare_coeff_0
  recurrence4LeadingSquare_coeff_1
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_154
  recurrence4LeadingSquare_coeff_155
  recurrence4LeadingSquare_coeff_156
  recurrence4LeadingSquare_coeff_157
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_211
  recurrence4LeadingSquare_coeff_212
  recurrence4LeadingSquare_coeff_213
  recurrence4LeadingSquare_coeff_214
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
  recurrence4LeadingSquare_coeff_27
  recurrence4LeadingSquare_coeff_28

attribute [local simp]
  recurrence4LeadingSquare_coeff_29
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

attribute [local simp]
  recurrence4LeadingSquare_coeff_87
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

private theorem recurrence4Scalar0Left_coeff_163_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (163 + x) *
        remainder4Coefficient0.coeff (163 - (163 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 163 + x
  · rw [recurrence4LeadingSquare_coeff_high (163 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (163 - (163 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_163 :
    recurrence4Scalar0Left.coeff 163 =
      -(((((12656 * 10 ^ 70 +
        0777806645448703861349552744758787599798449343863859163825089022705141) * 10 ^ 70 +
        6800408043601036814749578376781860628424102988931483383441501052318039) * 10 ^ 70 +
        4673968790819223432144008075316399718003201258591368054806635922384973) * 10 ^ 70 +
        9192527060055279323636656664423267262153065910530674584110377292154018) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 164,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (163 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_163_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_164_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (164 + x) *
        remainder4Coefficient0.coeff (164 - (164 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 164 + x
  · rw [recurrence4LeadingSquare_coeff_high (164 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (164 - (164 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_164 :
    recurrence4Scalar0Left.coeff 164 =
      (((((45055 * 10 ^ 70 +
        5023886982134648444622798295702295787443459386135358166122739615371057) * 10 ^ 70 +
        3404002836315062057249575288089452528515954160813142359098008237884186) * 10 ^ 70 +
        0730545957859554254714259612683933193662026557287213211337782431687809) * 10 ^ 70 +
        6709208771150360425202648264439162514899423068234051317016518455921952) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 165,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (164 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_164_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_165_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (165 + x) *
        remainder4Coefficient0.coeff (165 - (165 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 165 + x
  · rw [recurrence4LeadingSquare_coeff_high (165 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (165 - (165 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_165 :
    recurrence4Scalar0Left.coeff 165 =
      -(((((157905 * 10 ^ 70 +
        4978525256935031620415861891903657111043589765387914170051756083212428) * 10 ^ 70 +
        4276879427139099367103721944044177090317291579760895049148957458256510) * 10 ^ 70 +
        6647524794784505196483838781159740721546880951887164376076132475115076) * 10 ^ 70 +
        4648799222303829796137530683315983218998153160851294317899942189627999) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 166,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (165 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_165_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_166_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (166 + x) *
        remainder4Coefficient0.coeff (166 - (166 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 166 + x
  · rw [recurrence4LeadingSquare_coeff_high (166 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (166 - (166 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_166 :
    recurrence4Scalar0Left.coeff 166 =
      (((((544852 * 10 ^ 70 +
        5782991011257407187455527779072846643492056296178528524539488959280714) * 10 ^ 70 +
        6180786861197125752200367606983094516633195489300065076426644121932949) * 10 ^ 70 +
        9459917982966928229294089256508929263031864679114417955446105372798798) * 10 ^ 70 +
        8965020031523185574488079961445725008758000939785112044499362999107215) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 167,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (166 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_166_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_167_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (167 + x) *
        remainder4Coefficient0.coeff (167 - (167 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 167 + x
  · rw [recurrence4LeadingSquare_coeff_high (167 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (167 - (167 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_167 :
    recurrence4Scalar0Left.coeff 167 =
      -(((((1851074 * 10 ^ 70 +
        2069920784770314113862513072513572817959928906532488814963135084587679) * 10 ^ 70 +
        5569553334769236210000871299005189766792315877519647826338752185457574) * 10 ^ 70 +
        4508114363030141374710664252328114341084119377187425594072449414442452) * 10 ^ 70 +
        1259068336794265643970318441408887546974472852752678882309156153717030) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 168,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (167 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_167_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_168_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (168 + x) *
        remainder4Coefficient0.coeff (168 - (168 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 168 + x
  · rw [recurrence4LeadingSquare_coeff_high (168 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (168 - (168 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_168 :
    recurrence4Scalar0Left.coeff 168 =
      (((((6192436 * 10 ^ 70 +
        0178880103313770417086381523525989607981398130789866206334054096028841) * 10 ^ 70 +
        9202484331608533800109197921396670710464937256946838549607096977360444) * 10 ^ 70 +
        9734233028664144842642576748718697564207925213911754647279737482632805) * 10 ^ 70 +
        2781627860065270100810765033154050936847006831807541633512468363094184) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 169,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (168 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_168_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_169_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (169 + x) *
        remainder4Coefficient0.coeff (169 - (169 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 169 + x
  · rw [recurrence4LeadingSquare_coeff_high (169 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (169 - (169 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_169 :
    recurrence4Scalar0Left.coeff 169 =
      -(((((20399571 * 10 ^ 70 +
        7279818231960837132542741814576231197526117521506443182830804590574769) * 10 ^ 70 +
        4770585052736303092394283595507856079753738995542055966838571676635540) * 10 ^ 70 +
        7418981437117806900805621673305514220022312654472225174986190893696769) * 10 ^ 70 +
        7638999820202057162265670972827629243959145300747297551382986180514170) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 170,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (169 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_169_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_170_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (170 + x) *
        remainder4Coefficient0.coeff (170 - (170 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 170 + x
  · rw [recurrence4LeadingSquare_coeff_high (170 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (170 - (170 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_170 :
    recurrence4Scalar0Left.coeff 170 =
      (((((66180566 * 10 ^ 70 +
        5860315762723590948730976475652732823900807202484046588848708668683904) * 10 ^ 70 +
        4696310733971679673408672512044288720371926472744805776166732233412408) * 10 ^ 70 +
        3480685257098345550649271974035712111636795748059899960036715203436953) * 10 ^ 70 +
        1772684747742535136961357496744389490753528230209526726546481516214113) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 171,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (170 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_170_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_171_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (171 + x) *
        remainder4Coefficient0.coeff (171 - (171 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 171 + x
  · rw [recurrence4LeadingSquare_coeff_high (171 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (171 - (171 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_171 :
    recurrence4Scalar0Left.coeff 171 =
      -(((((211454566 * 10 ^ 70 +
        1079103980463304971962081157398149527361183528229754308049030623545575) * 10 ^ 70 +
        6368908390997761231038568103519425778682668028529981611875674557159994) * 10 ^ 70 +
        6904580044656762888624982144496234778375241594791452449645439592141124) * 10 ^ 70 +
        6445625017508530524512973376755234307429416543537188270418694373120430) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (171 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_171_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_172_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (172 + x) *
        remainder4Coefficient0.coeff (172 - (172 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 172 + x
  · rw [recurrence4LeadingSquare_coeff_high (172 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (172 - (172 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_172 :
    recurrence4Scalar0Left.coeff 172 =
      (((((665437443 * 10 ^ 70 +
        0233694934183728039345308200276541796939196658640850815417290900632892) * 10 ^ 70 +
        3965193350600184936513452441881057717263508189559055150834833169759295) * 10 ^ 70 +
        5384396797941975002244929918360736740545981830955024391498664909137008) * 10 ^ 70 +
        7910045852720843795576284428604939679777381477207696698687140188431971) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (172 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_172_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_173_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (173 + x) *
        remainder4Coefficient0.coeff (173 - (173 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 173 + x
  · rw [recurrence4LeadingSquare_coeff_high (173 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (173 - (173 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_173 :
    recurrence4Scalar0Left.coeff 173 =
      -(((((2062655024 * 10 ^ 70 +
        8531462457559524802315211694796544202047659788682342325853505662880579) * 10 ^ 70 +
        6811935832971263667684987510508357119614286971088203975952477279414731) * 10 ^ 70 +
        6691206413909836915701536794278182523941708628440532606236079664922543) * 10 ^ 70 +
        2057402757144292337644615083626274097800439130634789614303392160112600) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (173 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_173_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_174_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (174 + x) *
        remainder4Coefficient0.coeff (174 - (174 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 174 + x
  · rw [recurrence4LeadingSquare_coeff_high (174 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (174 - (174 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_174 :
    recurrence4Scalar0Left.coeff 174 =
      (((((6297961348 * 10 ^ 70 +
        2981242774409599385507480641222334844842831083269440294660181184873685) * 10 ^ 70 +
        3686017165729718634649870633425803906689600244159269761070703190918504) * 10 ^ 70 +
        3756498330028419685140520765676833315034004064969963936840494384241279) * 10 ^ 70 +
        0865030140515012822972947313850270903717884301459743844733286412472040) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (174 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_174_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_175_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (175 + x) *
        remainder4Coefficient0.coeff (175 - (175 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 175 + x
  · rw [recurrence4LeadingSquare_coeff_high (175 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (175 - (175 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_175 :
    recurrence4Scalar0Left.coeff 175 =
      -(((((18943117965 * 10 ^ 70 +
        6328817176869866504803137270900077514968828134224359666452292284201143) * 10 ^ 70 +
        5874598221623581649294065638616115889148952198722657702094871877437514) * 10 ^ 70 +
        3060505419954813083214216505120607531689163508655638009201308533789489) * 10 ^ 70 +
        1350952541914709228577845803058360330849796926056670142418343285509051) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (175 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_175_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_176_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (176 + x) *
        remainder4Coefficient0.coeff (176 - (176 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 176 + x
  · rw [recurrence4LeadingSquare_coeff_high (176 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (176 - (176 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_176 :
    recurrence4Scalar0Left.coeff 176 =
      (((((56131198005 * 10 ^ 70 +
        4603014987189838053623290575347190282171986377320725777796427158085311) * 10 ^ 70 +
        0739305401033732437322863647055581483335980072179707643302111951634203) * 10 ^ 70 +
        1767576304362305162878661758067479002426670398944473556863630951006891) * 10 ^ 70 +
        7158554321779521747666630067560228485519480391566660364944287685104894) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (176 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_176_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (177 + x) *
        remainder4Coefficient0.coeff (177 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 177 + x
  · rw [recurrence4LeadingSquare_coeff_high (177 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (177 - (177 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_177 :
    recurrence4Scalar0Left.coeff 177 =
      -(((((163863067878 * 10 ^ 70 +
        4882175770180708262598271374056230470169952398702448885819882928525917) * 10 ^ 70 +
        0342887422045194384796889119777972483355942296396446909386533018096391) * 10 ^ 70 +
        2473834082448541781512979181554893907704821915938598199844950406580139) * 10 ^ 70 +
        8622053289179454423969503612502716916727597412885480658133022470563103) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (177 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (178 + x) *
        remainder4Coefficient0.coeff (178 - (178 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 178 + x
  · rw [recurrence4LeadingSquare_coeff_high (178 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (178 - (178 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_178 :
    recurrence4Scalar0Left.coeff 178 =
      (((((471306672772 * 10 ^ 70 +
        9892942295281089802624855281995718000751813958150281470103538897340740) * 10 ^ 70 +
        2568820239586346400230654463057997773051076419640011948802982012351740) * 10 ^ 70 +
        6846591926650979824927147921085952428204665998767651229448679812342398) * 10 ^ 70 +
        7207660651847893391961388209452342868088910924672495428162407992177196) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (178 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (179 + x) *
        remainder4Coefficient0.coeff (179 - (179 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 179 + x
  · rw [recurrence4LeadingSquare_coeff_high (179 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (179 - (179 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_179 :
    recurrence4Scalar0Left.coeff 179 =
      -(((((1335650792743 * 10 ^ 70 +
        1836033655199476243829088399919647673503113793553264236832058299425249) * 10 ^ 70 +
        8152008677127662449013478957918841856105445703410866895045283611850675) * 10 ^ 70 +
        9739909736862991541418566722713123218722072837045339117715226653935852) * 10 ^ 70 +
        8179774508419807290323392965865710124174596607722375437949483056266494) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (179 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (180 + x) *
        remainder4Coefficient0.coeff (180 - (180 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 180 + x
  · rw [recurrence4LeadingSquare_coeff_high (180 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (180 - (180 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_180 :
    recurrence4Scalar0Left.coeff 180 =
      (((((3729662032582 * 10 ^ 70 +
        4867518539859930419101306715673405858105071316745211600169332275042427) * 10 ^ 70 +
        4535414395792162132621732533379649325696666449740273452782923114751180) * 10 ^ 70 +
        5436496918806813004473081246800153532499763283450955240702631460051056) * 10 ^ 70 +
        6970615854764561901188470633557266367415747795047882797031477531399744) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (180 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (181 + x) *
        remainder4Coefficient0.coeff (181 - (181 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 181 + x
  · rw [recurrence4LeadingSquare_coeff_high (181 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (181 - (181 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_181 :
    recurrence4Scalar0Left.coeff 181 =
      -(((((10262494455177 * 10 ^ 70 +
        7305296701270846246601523265047265287957331450904107689528502254467774) * 10 ^ 70 +
        8074133278440317638163367885082028282602021758427742767876527400691864) * 10 ^ 70 +
        7919724416812063901247095982350639668106760147570174002508653508384707) * 10 ^ 70 +
        4879056338790925999557911104312675969587540174026876357871022066452819) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (181 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (182 + x) *
        remainder4Coefficient0.coeff (182 - (182 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 182 + x
  · rw [recurrence4LeadingSquare_coeff_high (182 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (182 - (182 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_182 :
    recurrence4Scalar0Left.coeff 182 =
      (((((27826737668887 * 10 ^ 70 +
        9557956187621655786428391048822358372398725186056894260591286192372741) * 10 ^ 70 +
        0804215135487541320843489534375617298584144737374769483465974245517814) * 10 ^ 70 +
        2227126686073790290115201461659318460617508999083990831989294763888123) * 10 ^ 70 +
        4632744154405616145225236515671264085191369417114167394956758896573967) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (182 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (183 + x) *
        remainder4Coefficient0.coeff (183 - (183 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 183 + x
  · rw [recurrence4LeadingSquare_coeff_high (183 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (183 - (183 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_183 :
    recurrence4Scalar0Left.coeff 183 =
      -(((((74355975644912 * 10 ^ 70 +
        8478327469430422522941859003090302226475955299528642510975308591183523) * 10 ^ 70 +
        2430576912962238343009441640185392867377615117108975851478795016955621) * 10 ^ 70 +
        4482347386848532580410840821495791347588920961194123956867793473957262) * 10 ^ 70 +
        9327339193444628295450753899577744020000513174047731953612741370334478) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (183 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (184 + x) *
        remainder4Coefficient0.coeff (184 - (184 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 184 + x
  · rw [recurrence4LeadingSquare_coeff_high (184 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (184 - (184 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_184 :
    recurrence4Scalar0Left.coeff 184 =
      (((((195808408126996 * 10 ^ 70 +
        8658266067254605652378450131078306476537367295250789669857596451665158) * 10 ^ 70 +
        4251104981339227665872984631047693687525174831763431822656019348773393) * 10 ^ 70 +
        3830786949024437601006168602394994300669514263409950533967097646942656) * 10 ^ 70 +
        0899008347854349617900767673778805121130352691345139608951891276652907) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (184 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (185 + x) *
        remainder4Coefficient0.coeff (185 - (185 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 185 + x
  · rw [recurrence4LeadingSquare_coeff_high (185 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (185 - (185 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_185 :
    recurrence4Scalar0Left.coeff 185 =
      -(((((508189476112890 * 10 ^ 70 +
        3052448872818012376507223084028064130052337898533663849336972259978258) * 10 ^ 70 +
        9919643733916472554110710662190245861973115964956904477059817824019767) * 10 ^ 70 +
        6815557802337764707351928749885269506973864866691331228404556293166606) * 10 ^ 70 +
        8243987062421607255352065999601507063648055886654406231722771226133606) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (185 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (186 + x) *
        remainder4Coefficient0.coeff (186 - (186 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 186 + x
  · rw [recurrence4LeadingSquare_coeff_high (186 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (186 - (186 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_186 :
    recurrence4Scalar0Left.coeff 186 =
      (((((1299915755132334 * 10 ^ 70 +
        5492245477743175253739341496276495266089785972154407699783377069555727) * 10 ^ 70 +
        5475507524468959099341285471608896626210086312137513614230917377878257) * 10 ^ 70 +
        3139556732715745032871634668646347004630697845273919794811125421382409) * 10 ^ 70 +
        2850299429028716459939128831328862651356884391969354638100444500918668) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (186 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (187 + x) *
        remainder4Coefficient0.coeff (187 - (187 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 187 + x
  · rw [recurrence4LeadingSquare_coeff_high (187 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (187 - (187 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_187 :
    recurrence4Scalar0Left.coeff 187 =
      -(((((3277295871809373 * 10 ^ 70 +
        9515116964041466851632241106098963837068546697235906666907802353256298) * 10 ^ 70 +
        1370856024171806730469212518224220658520423011562963275955817977582978) * 10 ^ 70 +
        5707480868001546087768825394640796215931489806794787745052031258307105) * 10 ^ 70 +
        9055545773659039332704788268255926120768388187381707121401840964541434) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (187 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (188 + x) *
        remainder4Coefficient0.coeff (188 - (188 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 188 + x
  · rw [recurrence4LeadingSquare_coeff_high (188 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (188 - (188 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_188 :
    recurrence4Scalar0Left.coeff 188 =
      (((((8144080361628203 * 10 ^ 70 +
        4596963896828314553195265914726085012870706248409414513805628632518012) * 10 ^ 70 +
        5823498951000382488715952167152335831539008661789618522933945048178245) * 10 ^ 70 +
        5264302814080027396111683448088863065751448059599393153014966325094646) * 10 ^ 70 +
        4932990333461206884306744530273822326246279211455130762962027207948545) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (188 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (189 + x) *
        remainder4Coefficient0.coeff (189 - (189 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 189 + x
  · rw [recurrence4LeadingSquare_coeff_high (189 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (189 - (189 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_189 :
    recurrence4Scalar0Left.coeff 189 =
      -(((((19948434704419600 * 10 ^ 70 +
        2023802610467813690538269055402674283544198682810320011437275961786720) * 10 ^ 70 +
        5330465796598726121915614945830659387775816400872000007339096937896724) * 10 ^ 70 +
        6325122159964929678860300999776974247384208080230760850753058401362150) * 10 ^ 70 +
        5280105683416462547634523652353674905805587504601896591833980270341676) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (189 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (190 + x) *
        remainder4Coefficient0.coeff (190 - (190 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 190 + x
  · rw [recurrence4LeadingSquare_coeff_high (190 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (190 - (190 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_190 :
    recurrence4Scalar0Left.coeff 190 =
      (((((48164799521073356 * 10 ^ 70 +
        2636988131917120153895704564052050579748146414080773455070192314855056) * 10 ^ 70 +
        2144136852593929573061257706168630517271876495775151309656522732800906) * 10 ^ 70 +
        4561095893098285069027911100761413592247027027450768116076444208895973) * 10 ^ 70 +
        9711080526193516595495682913856803311207687411277303436409083598223204) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (190 - x)) = _
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
  rw [recurrence4Scalar0Left_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (191 + x) *
        remainder4Coefficient0.coeff (191 - (191 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 191 + x
  · rw [recurrence4LeadingSquare_coeff_high (191 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (191 - (191 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_191 :
    recurrence4Scalar0Left.coeff 191 =
      -(((((114635204400698466 * 10 ^ 70 +
        4904135320383869521524360933746848323329088986923339928696246408437849) * 10 ^ 70 +
        5893127208544983724664579164291161283022624455897783957044300958598333) * 10 ^ 70 +
        9261925054538661000372215633719628989876677003969715800034646585833299) * 10 ^ 70 +
        4045930621979266438803602504315325639514478886086125529546857620273022) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (191 - x)) = _
  rw [show 192 = 0 +
    192 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 192 = 32 +
      160 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 160 = 32 +
      128 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 128 = 32 +
      96 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 96 = 32 +
      64 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 64 = 32 +
      32 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 32 = 31 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (192 + x) *
        remainder4Coefficient0.coeff (192 - (192 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 192 + x
  · rw [recurrence4LeadingSquare_coeff_high (192 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (192 - (192 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_192 :
    recurrence4Scalar0Left.coeff 192 =
      (((((268959021318884325 * 10 ^ 70 +
        3115875796931118003297423114593685159066435973400230219242709519443376) * 10 ^ 70 +
        8638549390728658368053392402027000891381379301617966425853966542591074) * 10 ^ 70 +
        7011040693678147738578025556420852684654900985095247577415111842175461) * 10 ^ 70 +
        2901447079143204745618106348477341307077453546669622660354425674542757) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (192 - x)) = _
  rw [show 193 = 0 +
    193 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 32 +
      33 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 33 = 32 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (193 + x) *
        remainder4Coefficient0.coeff (193 - (193 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 193 + x
  · rw [recurrence4LeadingSquare_coeff_high (193 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (193 - (193 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_193 :
    recurrence4Scalar0Left.coeff 193 =
      -(((((622079637552590887 * 10 ^ 70 +
        4413687491115518730238730752884431102648317678374297714320657614591981) * 10 ^ 70 +
        5834892390007601181148142193014600615186431785403884077410694599864470) * 10 ^ 70 +
        0009150536151890478504320896395519059009846482081301615316143014012662) * 10 ^ 70 +
        3556219653838139246403761626747615645291250665393170071561204194703565) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (193 - x)) = _
  rw [show 194 = 0 +
    194 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 32 +
      34 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 34 = 32 +
      2 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 2 = 1 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (194 + x) *
        remainder4Coefficient0.coeff (194 - (194 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 194 + x
  · rw [recurrence4LeadingSquare_coeff_high (194 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (194 - (194 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_194 :
    recurrence4Scalar0Left.coeff 194 =
      (((((1418433264697527325 * 10 ^ 70 +
        1756284500983973101431852375850653986806343099544932665219377197734885) * 10 ^ 70 +
        2119334441427195911199541333965017553605305546917618712581074933591539) * 10 ^ 70 +
        1694184713666423363330394305609129937935245165579166193428412102746432) * 10 ^ 70 +
        6789985308429876595252578449198903158676787922311398157848849122086311) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (194 - x)) = _
  rw [show 195 = 0 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  norm_num only [Finset.sum_range_zero, zero_add]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (195 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (195 + x) *
        remainder4Coefficient0.coeff (195 - (195 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 195 + x
  · rw [recurrence4LeadingSquare_coeff_high (195 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (195 - (195 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_195 :
    recurrence4Scalar0Left.coeff 195 =
      -(((((3188493571244610522 * 10 ^ 70 +
        3805752416875197365614218221472086786575396866515936287480343835449962) * 10 ^ 70 +
        1365826094586635047257865813869312639922372015399699299446360107148903) * 10 ^ 70 +
        7414258693151800718469935703218447465938865988883634553410595526664688) * 10 ^ 70 +
        2562356080519371042392599886714364421791330884499831872408204259774600) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (195 - x)) = _
  rw [show 196 = 1 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (196 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (196 + x) *
        remainder4Coefficient0.coeff (196 - (196 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 196 + x
  · rw [recurrence4LeadingSquare_coeff_high (196 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (196 - (196 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_196 :
    recurrence4Scalar0Left.coeff 196 =
      (((((7066200232205532493 * 10 ^ 70 +
        7375248275990946729350270636195526687743226467291060122672166340040280) * 10 ^ 70 +
        3671798099876157898464429146659823032194823764408921141889520553912769) * 10 ^ 70 +
        9857800838242989195400804436686779692910417141513954593624129204753982) * 10 ^ 70 +
        8665842337520507520806535478338257597526571542648927158396877943092078) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (196 - x)) = _
  rw [show 197 = 2 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (197 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (197 + x) *
        remainder4Coefficient0.coeff (197 - (197 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 197 + x
  · rw [recurrence4LeadingSquare_coeff_high (197 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (197 - (197 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_197 :
    recurrence4Scalar0Left.coeff 197 =
      -(((((15439011906801270379 * 10 ^ 70 +
        5115747968887426344151419642126433956830562183526977175621541090425019) * 10 ^ 70 +
        5512589963466620538127490426577413204703019886278537682368761873072155) * 10 ^ 70 +
        2281700058920708794166194710144839541004239831303477677695507939913028) * 10 ^ 70 +
        6675807817199442010006601787497536044778998435523713633932252117620977) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (197 - x)) = _
  rw [show 198 = 3 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (198 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (198 + x) *
        remainder4Coefficient0.coeff (198 - (198 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 198 + x
  · rw [recurrence4LeadingSquare_coeff_high (198 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (198 - (198 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_198 :
    recurrence4Scalar0Left.coeff 198 =
      (((((33257914628450569216 * 10 ^ 70 +
        9953184060671270722236907963573228920313485650025457926498162934431285) * 10 ^ 70 +
        1409784553003536510236729728045071288236300340689849686484479685326035) * 10 ^ 70 +
        3639739180091728623417018838111436326097805904930741044844001138985231) * 10 ^ 70 +
        9529078409228173095797150781439246655521284517123055234557744032772876) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (198 - x)) = _
  rw [show 199 = 4 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (199 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (199 + x) *
        remainder4Coefficient0.coeff (199 - (199 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 199 + x
  · rw [recurrence4LeadingSquare_coeff_high (199 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (199 - (199 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_199 :
    recurrence4Scalar0Left.coeff 199 =
      -(((((70635109148660598865 * 10 ^ 70 +
        7831088808310211381553568020464655018687879729788184469226580235293776) * 10 ^ 70 +
        0691513496804256948107266797810294773494930265986143069994333430479169) * 10 ^ 70 +
        2428189851264866360651992465953899817558901630991382205028659187558732) * 10 ^ 70 +
        8515148885721237656909025215334976429934133721133947119748994438297966) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (199 - x)) = _
  rw [show 200 = 5 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (200 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (200 + x) *
        remainder4Coefficient0.coeff (200 - (200 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 200 + x
  · rw [recurrence4LeadingSquare_coeff_high (200 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (200 - (200 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_200 :
    recurrence4Scalar0Left.coeff 200 =
      (((((147912140974087865979 * 10 ^ 70 +
        0479504234434940321018413527068962809818786484054656621736528964767452) * 10 ^ 70 +
        0115193850697848004626767674901564994904134592736149506371321001199288) * 10 ^ 70 +
        7388833459430799275967234396428762719707412659266849602196591518123795) * 10 ^ 70 +
        5023670164292023353794791821480595501665015380750754503143259804485178) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (200 - x)) = _
  rw [show 201 = 6 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (201 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (201 + x) *
        remainder4Coefficient0.coeff (201 - (201 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 201 + x
  · rw [recurrence4LeadingSquare_coeff_high (201 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (201 - (201 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_201 :
    recurrence4Scalar0Left.coeff 201 =
      -(((((305387652476714851217 * 10 ^ 70 +
        8726244553138722222161441176951533667873583319060414278271495024374206) * 10 ^ 70 +
        0386104260826560933718559955735730022768011842116415082788507245931179) * 10 ^ 70 +
        7376368181003248043821170987817381126094333603018559602461765159184520) * 10 ^ 70 +
        1888932507194027129312732088852088249412921009369125807792897890981623) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (201 - x)) = _
  rw [show 202 = 7 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (202 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (202 + x) *
        remainder4Coefficient0.coeff (202 - (202 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 202 + x
  · rw [recurrence4LeadingSquare_coeff_high (202 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (202 - (202 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_202 :
    recurrence4Scalar0Left.coeff 202 =
      (((((621684102329259303825 * 10 ^ 70 +
        6307575504184334450330943419017025053417867476390977978973259802917952) * 10 ^ 70 +
        7221029206144589681167676213645827245782138921498063121608512666191214) * 10 ^ 70 +
        4290195435957858065791860217156924216882920580131360411026481787554451) * 10 ^ 70 +
        0571421063459929691806719979545822724212328569473207369362920591053056) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (202 - x)) = _
  rw [show 203 = 8 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (203 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (203 + x) *
        remainder4Coefficient0.coeff (203 - (203 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 203 + x
  · rw [recurrence4LeadingSquare_coeff_high (203 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (203 - (203 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_203 :
    recurrence4Scalar0Left.coeff 203 =
      -(((((1247855239297143657276 * 10 ^ 70 +
        8949007283882172431704778221567927160332252822149787449685199943630007) * 10 ^ 70 +
        0966992731224820038933323112756987405449596024625400719203717901096918) * 10 ^ 70 +
        2494519461099668684388267545722824536362671959966220999255200683182636) * 10 ^ 70 +
        2193869012004024500215161711456342004892012133892181230235171203531526) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (203 - x)) = _
  rw [show 204 = 9 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (204 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (204 + x) *
        remainder4Coefficient0.coeff (204 - (204 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 204 + x
  · rw [recurrence4LeadingSquare_coeff_high (204 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (204 - (204 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_204 :
    recurrence4Scalar0Left.coeff 204 =
      (((((2469674073580520829398 * 10 ^ 70 +
        9250779376201020001542004480422780370587899362676270807028469252529910) * 10 ^ 70 +
        0574165465367241926699420013326871474765404534560572221606580115967829) * 10 ^ 70 +
        4257839110086569366863765160281124089789836785966346431074846730615082) * 10 ^ 70 +
        7362772773174032665277024477139336695382789508973928561938719113570852) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (204 - x)) = _
  rw [show 205 = 10 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (205 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (205 + x) *
        remainder4Coefficient0.coeff (205 - (205 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 205 + x
  · rw [recurrence4LeadingSquare_coeff_high (205 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (205 - (205 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_205 :
    recurrence4Scalar0Left.coeff 205 =
      -(((((4819480226774865668639 * 10 ^ 70 +
        0652084572944446903763168140586306670808982392496448422133487780217939) * 10 ^ 70 +
        5984179974866956461075686584357090331655751037408954629832546540337941) * 10 ^ 70 +
        4401464677085398033746096609282938062170487320026171059320098029170248) * 10 ^ 70 +
        7054222194275182345810012056780512626534455226164813320957024485631308) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (205 - x)) = _
  rw [show 206 = 11 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (206 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (206 + x) *
        remainder4Coefficient0.coeff (206 - (206 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 206 + x
  · rw [recurrence4LeadingSquare_coeff_high (206 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (206 - (206 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_206 :
    recurrence4Scalar0Left.coeff 206 =
      (((((9273620160779271763050 * 10 ^ 70 +
        8016284350201892224253538048360572984885786735069149206222295687511753) * 10 ^ 70 +
        4033134351156847240158316344232134544281288208806232491196615895982064) * 10 ^ 70 +
        8271547925614852950275781163258949241603938636644001115422362158163747) * 10 ^ 70 +
        9879117356168325526526024648384868178596406921474350485456824134530290) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (206 - x)) = _
  rw [show 207 = 12 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (207 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (207 + x) *
        remainder4Coefficient0.coeff (207 - (207 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 207 + x
  · rw [recurrence4LeadingSquare_coeff_high (207 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (207 - (207 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_207 :
    recurrence4Scalar0Left.coeff 207 =
      -(((((17595014282008033135319 * 10 ^ 70 +
        5777965400516218212390131665388430790387624629047331055685654061264012) * 10 ^ 70 +
        4784372163788981394207708589323278320982959285395032800583976371478649) * 10 ^ 70 +
        3449557716160150660539063612720953605173314909431563975457545217203372) * 10 ^ 70 +
        1989021067857844793534515307184922014517411517574269854794702545481216) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (207 - x)) = _
  rw [show 208 = 13 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (208 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (208 + x) *
        remainder4Coefficient0.coeff (208 - (208 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 208 + x
  · rw [recurrence4LeadingSquare_coeff_high (208 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (208 - (208 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_208 :
    recurrence4Scalar0Left.coeff 208 =
      (((((32917214821474258480474 * 10 ^ 70 +
        2512412708750889031740488130706100234725550432221760719195595286932923) * 10 ^ 70 +
        6823318644389540225717772961117443618352083213496164429126635366577746) * 10 ^ 70 +
        8110307279264412664060894931829304657387541936099166983299817879914036) * 10 ^ 70 +
        0096743687063190143428132623360601545408800114399188347500396758291121) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (208 - x)) = _
  rw [show 209 = 14 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (209 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (209 + x) *
        remainder4Coefficient0.coeff (209 - (209 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 209 + x
  · rw [recurrence4LeadingSquare_coeff_high (209 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (209 - (209 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_209 :
    recurrence4Scalar0Left.coeff 209 =
      -(((((60722663223937046191165 * 10 ^ 70 +
        1095845692157995945185299502884822069449848117052515181207798052641971) * 10 ^ 70 +
        0668079539134519120871289715717576703820780076588960781225544243969471) * 10 ^ 70 +
        5929221693736490650104431175656418485159608031505175435128109063003425) * 10 ^ 70 +
        0003965312259274718789705690421634909321210505196682793170660518824520) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (209 - x)) = _
  rw [show 210 = 15 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (210 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (210 + x) *
        remainder4Coefficient0.coeff (210 - (210 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 210 + x
  · rw [recurrence4LeadingSquare_coeff_high (210 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (210 - (210 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_210 :
    recurrence4Scalar0Left.coeff 210 =
      (((((110451884533435134799970 * 10 ^ 70 +
        1319998484098973257194405751523143178256031116528664171040229033889220) * 10 ^ 70 +
        5498749473707919750250044467214799090000879943033606424380754825805534) * 10 ^ 70 +
        0508677957722914930851847263139846496862424343053718016371818722823293) * 10 ^ 70 +
        8470586087840686360291910338902315728421809779542008118244847261591737) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (210 - x)) = _
  rw [show 211 = 16 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (211 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (211 + x) *
        remainder4Coefficient0.coeff (211 - (211 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 211 + x
  · rw [recurrence4LeadingSquare_coeff_high (211 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (211 - (211 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_211 :
    recurrence4Scalar0Left.coeff 211 =
      -(((((198102297236079722626520 * 10 ^ 70 +
        8301763536680629772998248472156440387765799159545845036663173105031213) * 10 ^ 70 +
        3113157063738241236640543758997603831863351212812909522055796413489767) * 10 ^ 70 +
        4252268309451177547721474893362313620819095098369869136629680446831952) * 10 ^ 70 +
        7094521279505041240469474359165795058572224348178594817778901389450384) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (211 - x)) = _
  rw [show 212 = 17 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (212 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (212 + x) *
        remainder4Coefficient0.coeff (212 - (212 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 212 + x
  · rw [recurrence4LeadingSquare_coeff_high (212 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (212 - (212 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_212 :
    recurrence4Scalar0Left.coeff 212 =
      (((((350347114117479612891873 * 10 ^ 70 +
        3933144408697091486378906482390532970478954754728535507807226313894694) * 10 ^ 70 +
        9197545597968087473399475906233425144705583145059515199129744464115039) * 10 ^ 70 +
        6770413065978976294259840534126899177304472306628334803210799676572586) * 10 ^ 70 +
        7007650142814157083033620283988868739798075588855567515406974969853243) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (212 - x)) = _
  rw [show 213 = 18 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (213 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (213 + x) *
        remainder4Coefficient0.coeff (213 - (213 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 213 + x
  · rw [recurrence4LeadingSquare_coeff_high (213 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (213 - (213 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_213 :
    recurrence4Scalar0Left.coeff 213 =
      -(((((610939061002311366871054 * 10 ^ 70 +
        4601574860754658604960546710521419693874906438716628513258224292420601) * 10 ^ 70 +
        3652338725800476188187518804771658495923729744781260756064804764755493) * 10 ^ 70 +
        9074797264699888869911711686272761609411916869157712556619378294092842) * 10 ^ 70 +
        3404814612012672068706976632262188415369523560043400121102983917355866) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (213 - x)) = _
  rw [show 214 = 19 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (214 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (214 + x) *
        remainder4Coefficient0.coeff (214 - (214 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 214 + x
  · rw [recurrence4LeadingSquare_coeff_high (214 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (214 - (214 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_214 :
    recurrence4Scalar0Left.coeff 214 =
      (((((1050471445634654692440844 * 10 ^ 70 +
        6338002513760944924437792895236776172304461651014553346654026746186973) * 10 ^ 70 +
        0731531905272412969071579894931650059571041559432420623207037152463720) * 10 ^ 70 +
        8039114079302808247227023805726405102463260607619031602858023485434680) * 10 ^ 70 +
        1274878770449042391977324808356801777214023642821588098463336671296611) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (214 - x)) = _
  rw [show 215 = 20 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (215 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (215 + x) *
        remainder4Coefficient0.coeff (215 - (215 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 215 + x
  · rw [recurrence4LeadingSquare_coeff_high (215 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (215 - (215 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_215 :
    recurrence4Scalar0Left.coeff 215 =
      -(((((1780956418878576874918269 * 10 ^ 70 +
        6887176390213930720759768215869176227697705498971581235526948198421466) * 10 ^ 70 +
        3524089317948948949221426799070217875929240540716285200606878452056025) * 10 ^ 70 +
        5983424331029051152788089414134010746707610604555953592635153352302544) * 10 ^ 70 +
        0881357609289705834506214559091264405966971847972064501484266233033394) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (215 - x)) = _
  rw [show 216 = 21 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (216 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (216 + x) *
        remainder4Coefficient0.coeff (216 - (216 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 216 + x
  · rw [recurrence4LeadingSquare_coeff_high (216 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (216 - (216 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_216 :
    recurrence4Scalar0Left.coeff 216 =
      (((((2977142380303626194330639 * 10 ^ 70 +
        4664676012609788226542435303097140348103064743780051238257259034443342) * 10 ^ 70 +
        3540457382831723165716632014270354870826487025614387327400691789779799) * 10 ^ 70 +
        8275187975920722105040062408625361492916047413498256512465429528109803) * 10 ^ 70 +
        4377370009135114240078981087017444961903461373169423728707186415144087) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (216 - x)) = _
  rw [show 217 = 22 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (217 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (217 + x) *
        remainder4Coefficient0.coeff (217 - (217 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 217 + x
  · rw [recurrence4LeadingSquare_coeff_high (217 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (217 - (217 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_217 :
    recurrence4Scalar0Left.coeff 217 =
      -(((((4907006512027124825694696 * 10 ^ 70 +
        4360788449470543391352593357559324371532997014765489312614851224307574) * 10 ^ 70 +
        0004840351587780280615814796654332932193735720556190082871885320098861) * 10 ^ 70 +
        0883220577693617527980915200465894426816528135574530652163201532851242) * 10 ^ 70 +
        2340767964761077737863901364511006659816983229472885936066008906614467) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (217 - x)) = _
  rw [show 218 = 23 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (218 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (218 + x) *
        remainder4Coefficient0.coeff (218 - (218 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 218 + x
  · rw [recurrence4LeadingSquare_coeff_high (218 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (218 - (218 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_218 :
    recurrence4Scalar0Left.coeff 218 =
      (((((7974374040417756193387899 * 10 ^ 70 +
        4350530785925980003762518605256869661230600782445872700710954506389074) * 10 ^ 70 +
        0909579713470993820084218764236190464067501108819083918283712909157320) * 10 ^ 70 +
        7795763026108223349547733565405104256071372033045528067445994488959704) * 10 ^ 70 +
        1542839043665904170758248088080660832298535801059213099067081108898812) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (218 - x)) = _
  rw [show 219 = 24 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (219 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (219 + x) *
        remainder4Coefficient0.coeff (219 - (219 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 219 + x
  · rw [recurrence4LeadingSquare_coeff_high (219 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (219 - (219 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_219 :
    recurrence4Scalar0Left.coeff 219 =
      -(((((12777045072954391395530053 * 10 ^ 70 +
        2677770211651472552877846925681343252913274370540086290277348262726388) * 10 ^ 70 +
        9466968497705507726878627714349588340967412022895982755093793729233409) * 10 ^ 70 +
        9503677598017384549582715317966423378524546176654300955335240813691560) * 10 ^ 70 +
        5852662828250285087515106414629837202365607057754890565126300355110594) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (219 - x)) = _
  rw [show 220 = 25 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (220 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (220 + x) *
        remainder4Coefficient0.coeff (220 - (220 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 220 + x
  · rw [recurrence4LeadingSquare_coeff_high (220 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (220 - (220 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_220 :
    recurrence4Scalar0Left.coeff 220 =
      (((((20184017961789427838936863 * 10 ^ 70 +
        9128348005299073206901378993783251223779105153081289626684643877239640) * 10 ^ 70 +
        9775226045409115814297679144247848881621225266848572171898970749069137) * 10 ^ 70 +
        3927737202422403802495762512566632151461254007501000464426370911090732) * 10 ^ 70 +
        0014473807417654949316519831935434587457336522342579386268932989271287) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (220 - x)) = _
  rw [show 221 = 26 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (221 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (221 + x) *
        remainder4Coefficient0.coeff (221 - (221 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 221 + x
  · rw [recurrence4LeadingSquare_coeff_high (221 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (221 - (221 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_221 :
    recurrence4Scalar0Left.coeff 221 =
      -(((((31435198149363420891258849 * 10 ^ 70 +
        8709312953287477256844342844121146035545115168277668222281942513675673) * 10 ^ 70 +
        6722406835908170228201507429940946443723038969277884294472142229282500) * 10 ^ 70 +
        1153057582775590904868649756828116590710795801373352420773955292535653) * 10 ^ 70 +
        2737748558398910436076637207763692310346915104586652867341149779398231) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (221 - x)) = _
  rw [show 222 = 27 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (222 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (222 + x) *
        remainder4Coefficient0.coeff (222 - (222 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 222 + x
  · rw [recurrence4LeadingSquare_coeff_high (222 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (222 - (222 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_222 :
    recurrence4Scalar0Left.coeff 222 =
      (((((48266136709120727939969114 * 10 ^ 70 +
        4695465595965432015147331389778917672320761800005984819388412216719362) * 10 ^ 70 +
        4911683649469297389294183263191545812663091018207223069110115675594274) * 10 ^ 70 +
        0330949518408549334399780601442275544622620499120991605711059989666066) * 10 ^ 70 +
        3361074938388225905642801378965927269034743782680140621654404264202276) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (222 - x)) = _
  rw [show 223 = 28 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (223 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (223 + x) *
        remainder4Coefficient0.coeff (223 - (223 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 223 + x
  · rw [recurrence4LeadingSquare_coeff_high (223 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (223 - (223 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_223 :
    recurrence4Scalar0Left.coeff 223 =
      -(((((73058582090721344606745849 * 10 ^ 70 +
        3911707457148967167558624420246272309627652120350501694622633447291159) * 10 ^ 70 +
        2667625325350932692969780579221890870504969356273896578365164754146280) * 10 ^ 70 +
        4844033109539822115432853490254167286312173253316639636469928066306452) * 10 ^ 70 +
        4386493318792764836313258712876853965116155424728332143841906182641352) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (223 - x)) = _
  rw [show 224 = 29 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (224 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (224 + x) *
        remainder4Coefficient0.coeff (224 - (224 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 224 + x
  · rw [recurrence4LeadingSquare_coeff_high (224 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (224 - (224 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_224 :
    recurrence4Scalar0Left.coeff 224 =
      (((((109014678661831132949652721 * 10 ^ 70 +
        9032693816639599967778006981892610554319022034552684210971081469441903) * 10 ^ 70 +
        9712441565197280223515399101965902345358256850051187827620622946001299) * 10 ^ 70 +
        2607552791769099783742015904882468357496712740219615881946777294494164) * 10 ^ 70 +
        2559751660919031250140780077684971525570817945935384349244743855423823) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (224 - x)) = _
  rw [show 225 = 30 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (225 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (225 + x) *
        remainder4Coefficient0.coeff (225 - (225 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 225 + x
  · rw [recurrence4LeadingSquare_coeff_high (225 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (225 - (225 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_225 :
    recurrence4Scalar0Left.coeff 225 =
      -(((((160348284688458838024037851 * 10 ^ 70 +
        1615503289532133330396205077169449591666798983944932958411586143102769) * 10 ^ 70 +
        9770282567475088476063341634466360588501466064051583006359805047640422) * 10 ^ 70 +
        0993424116976683832374812991627881061048694878017124639350844466851786) * 10 ^ 70 +
        0356116266203407591742037652245792990274281477376119801369067518622440) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (225 - x)) = _
  rw [show 226 = 31 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (226 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (226 + x) *
        remainder4Coefficient0.coeff (226 - (226 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 226 + x
  · rw [recurrence4LeadingSquare_coeff_high (226 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (226 - (226 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_226 :
    recurrence4Scalar0Left.coeff 226 =
      (((((232481014947998064591179390 * 10 ^ 70 +
        2742066355360681988834428517564531035048111238759122247845732194754739) * 10 ^ 70 +
        3444710065060368705014595324360983194247889991686975089035917773188923) * 10 ^ 70 +
        5021967373423897545331747625292051201655562878870708312946570302088823) * 10 ^ 70 +
        4032743057485085902885745140722737762054817952416744408423429523101184) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (226 - x)) = _
  rw [show 227 = 32 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (227 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (227 + x) *
        remainder4Coefficient0.coeff (227 - (227 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 227 + x
  · rw [recurrence4LeadingSquare_coeff_high (227 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (227 - (227 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_227 :
    recurrence4Scalar0Left.coeff 227 =
      -(((((332223361990755450879626187 * 10 ^ 70 +
        7584248504375600892103928346921994860087921591751705013838646680970331) * 10 ^ 70 +
        6554229123994455304265918507010627522207123978698762834949193744602939) * 10 ^ 70 +
        1095438534506587680654749340413898155981268408785246859790868406259647) * 10 ^ 70 +
        1925427088821803417809346689656207033091085705863590420236347171172734) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (227 - x)) = _
  rw [show 228 = 33 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (228 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (228 + x) *
        remainder4Coefficient0.coeff (228 - (228 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 228 + x
  · rw [recurrence4LeadingSquare_coeff_high (228 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (228 - (228 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_228 :
    recurrence4Scalar0Left.coeff 228 =
      (((((467913053679788596871375474 * 10 ^ 70 +
        8643394215414815712772441131330737165412000397917170251575952957052470) * 10 ^ 70 +
        5991568770058920208401023230733940128181727642417849615789295917609442) * 10 ^ 70 +
        8373701102250701493590085272990052574461758163272127909590467937684545) * 10 ^ 70 +
        9319316697843539383916001676049396904199728097798498681205013123495505) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (228 - x)) = _
  rw [show 229 = 34 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (229 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (229 + x) *
        remainder4Coefficient0.coeff (229 - (229 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 229 + x
  · rw [recurrence4LeadingSquare_coeff_high (229 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (229 - (229 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_229 :
    recurrence4Scalar0Left.coeff 229 =
      -(((((649474501390019000430333795 * 10 ^ 70 +
        7040139729415785093867352475611488032207531773820869922610124340183791) * 10 ^ 70 +
        2917942745172149383081646812261619922572602285337673090410592430269023) * 10 ^ 70 +
        3049543122962095691355524484193536959973496371072974234276140896168426) * 10 ^ 70 +
        0729968514211827920192436378229407914202013477750203322534592360954308) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (229 - x)) = _
  rw [show 230 = 35 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (230 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (230 + x) *
        remainder4Coefficient0.coeff (230 - (230 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 230 + x
  · rw [recurrence4LeadingSquare_coeff_high (230 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (230 - (230 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_230 :
    recurrence4Scalar0Left.coeff 230 =
      (((((888356065632085432339464114 * 10 ^ 70 +
        4755064235170840726369242384881169170737309604651233321176295464290527) * 10 ^ 70 +
        7635385304628557597328819363701691445704425868480726871596074419977257) * 10 ^ 70 +
        1153223867165738631353057995459161052144142643106035754932467347826775) * 10 ^ 70 +
        0343892887064933963715619343274449736611724960233607804322440853800487) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (230 - x)) = _
  rw [show 231 = 36 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (231 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (231 + x) *
        remainder4Coefficient0.coeff (231 - (231 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 231 + x
  · rw [recurrence4LeadingSquare_coeff_high (231 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (231 - (231 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_231 :
    recurrence4Scalar0Left.coeff 231 =
      -(((((1197297614597242407367834505 * 10 ^ 70 +
        9440356542782625621323456654850467986515902814381274832873876160973460) * 10 ^ 70 +
        6542174885213364250558352175038214897410929654718548172902297860060840) * 10 ^ 70 +
        7030941553716513995870598855546331952434016265620814377313709817149245) * 10 ^ 70 +
        0096351417691594344956240154387537516271365879404026916189543368428148) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (231 - x)) = _
  rw [show 232 = 37 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (232 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (232 + x) *
        remainder4Coefficient0.coeff (232 - (232 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 232 + x
  · rw [recurrence4LeadingSquare_coeff_high (232 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (232 - (232 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_232 :
    recurrence4Scalar0Left.coeff 232 =
      (((((1589881469765176999536304747 * 10 ^ 70 +
        8363201218612274821013365241235199879954553947023492333753154236844636) * 10 ^ 70 +
        2544896811595264680429108593207277916344886187016653303699340683195737) * 10 ^ 70 +
        3408142972666612300311734732202451511977136458966708092551585174454496) * 10 ^ 70 +
        7154783063354774414673456306176947391657179459010789687629761149785051) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (232 - x)) = _
  rw [show 233 = 38 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (233 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (233 + x) *
        remainder4Coefficient0.coeff (233 - (233 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 233 + x
  · rw [recurrence4LeadingSquare_coeff_high (233 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (233 - (233 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_233 :
    recurrence4Scalar0Left.coeff 233 =
      -(((((2079827363212846869591803695 * 10 ^ 70 +
        1456928937969553305891144635303082897645034607816453387833356094376269) * 10 ^ 70 +
        5620586241107340586606743515360213405756899625588123734855671656423574) * 10 ^ 70 +
        7524018889059978153896659749491334524351695918886473101618586079064365) * 10 ^ 70 +
        2901481984165738001973019205882982328809555352745225605300449664508565) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (233 - x)) = _
  rw [show 234 = 39 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (234 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (234 + x) *
        remainder4Coefficient0.coeff (234 - (234 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 234 + x
  · rw [recurrence4LeadingSquare_coeff_high (234 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (234 - (234 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_234 :
    recurrence4Scalar0Left.coeff 234 =
      (((((2680008199558482805900443853 * 10 ^ 70 +
        2958695661037032638225207924231219639079242075075814799640690065817594) * 10 ^ 70 +
        0166385098070639285537651626434889356921315251498037969483260898360711) * 10 ^ 70 +
        4585069195949183277084803965212439789358627526754164294200506428722182) * 10 ^ 70 +
        6027506286997101597730829752128157637499184955363777013566196936580058) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (234 - x)) = _
  rw [show 235 = 40 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (235 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (235 + x) *
        remainder4Coefficient0.coeff (235 - (235 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 235 + x
  · rw [recurrence4LeadingSquare_coeff_high (235 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (235 - (235 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_235 :
    recurrence4Scalar0Left.coeff 235 =
      -(((((3401189174421757435688943227 * 10 ^ 70 +
        7266443527518090910388894614419516110961080777743150640860852410732544) * 10 ^ 70 +
        2214954739566645266243657463789504514642552163679996158801907838089453) * 10 ^ 70 +
        3892745849627752143708879480315374543515922849718703541363584082189121) * 10 ^ 70 +
        9565487298040937249221926757506163479639599899924059913972026911028730) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (235 - x)) = _
  rw [show 236 = 41 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (236 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (236 + x) *
        remainder4Coefficient0.coeff (236 - (236 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 236 + x
  · rw [recurrence4LeadingSquare_coeff_high (236 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (236 - (236 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_236 :
    recurrence4Scalar0Left.coeff 236 =
      (((((4250527841226941337522191356 * 10 ^ 70 +
        1029817521708661699932959391339205183056924134276699241361043384497383) * 10 ^ 70 +
        9427829266181451042179635957627636753238955910142206019914986818811604) * 10 ^ 70 +
        7383374685620327640729297339900346357904285207325456485474798664379187) * 10 ^ 70 +
        6542057318631725482742210226954034155786578684032487873329937217665234) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (236 - x)) = _
  rw [show 237 = 42 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (237 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (237 + x) *
        remainder4Coefficient0.coeff (237 - (237 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 237 + x
  · rw [recurrence4LeadingSquare_coeff_high (237 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (237 - (237 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_237 :
    recurrence4Scalar0Left.coeff 237 =
      -(((((5229915038182535052830673309 * 10 ^ 70 +
        7601058061366438416560079355376410749162966962183663509952091194027129) * 10 ^ 70 +
        8540484520902281381728743074512527340399756090352771384942896821293033) * 10 ^ 70 +
        1722735343179504892140834374443071109521850762682135781899604100232901) * 10 ^ 70 +
        8160224104934480569284024785901343827061052932249545671179244022150627) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (237 - x)) = _
  rw [show 238 = 43 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (238 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (238 + x) *
        remainder4Coefficient0.coeff (238 - (238 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 238 + x
  · rw [recurrence4LeadingSquare_coeff_high (238 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (238 - (238 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_238 :
    recurrence4Scalar0Left.coeff 238 =
      (((((6334282242554818773618283400 * 10 ^ 70 +
        9154540752679076951577068195068903087694930563193367531555110451858382) * 10 ^ 70 +
        1876750882701339704842266465182383785467279305369409163156673096217691) * 10 ^ 70 +
        0676755372613987887499699012762065183999599843006849837754651424713409) * 10 ^ 70 +
        1017819453031010578940545837992816364907046669140719637784592562551335) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (238 - x)) = _
  rw [show 239 = 44 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (239 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (239 + x) *
        remainder4Coefficient0.coeff (239 - (239 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 239 + x
  · rw [recurrence4LeadingSquare_coeff_high (239 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (239 - (239 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_239 :
    recurrence4Scalar0Left.coeff 239 =
      -(((((7550044063731309642118421872 * 10 ^ 70 +
        7887465257411203340305982013659654620101126820132914031180279910723849) * 10 ^ 70 +
        9729636969673618415388602579618372005117288626842354922951786494975671) * 10 ^ 70 +
        7503305917837954343268292256351446695751431235759759561667392798641127) * 10 ^ 70 +
        8140933567177665824259888326304577463383327028279325835285103023772802) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (239 - x)) = _
  rw [show 240 = 45 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (240 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (240 + x) *
        remainder4Coefficient0.coeff (240 - (240 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 240 + x
  · rw [recurrence4LeadingSquare_coeff_high (240 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (240 - (240 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_240 :
    recurrence4Scalar0Left.coeff 240 =
      (((((8853877904193264850866750004 * 10 ^ 70 +
        7535379059667143824207996012356686320257927351306911388643566016260599) * 10 ^ 70 +
        1303985014529419188005081925667359261847848864235785631261347685248043) * 10 ^ 70 +
        9086653655114698714406016940242799928958755793116133231204156150371481) * 10 ^ 70 +
        6591730670247491333372190303252561365160377043490703480713397228057252) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (240 - x)) = _
  rw [show 241 = 46 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (241 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (241 + x) *
        remainder4Coefficient0.coeff (241 - (241 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 241 + x
  · rw [recurrence4LeadingSquare_coeff_high (241 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (241 - (241 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_241 :
    recurrence4Scalar0Left.coeff 241 =
      -(((((10212058382327316501748075198 * 10 ^ 70 +
        6351964010935593776584647378212838573614969739588184205308341460076224) * 10 ^ 70 +
        6683225571981111001938229046031462292104595876271472898367504457936077) * 10 ^ 70 +
        9881512288774435056493250306930808120627349848356815624018117432121324) * 10 ^ 70 +
        2487602916640027050807167819611128826123510377368225843490611841483265) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (241 - x)) = _
  rw [show 242 = 47 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (242 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (242 + x) *
        remainder4Coefficient0.coeff (242 - (242 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 242 + x
  · rw [recurrence4LeadingSquare_coeff_high (242 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (242 - (242 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_242 :
    recurrence4Scalar0Left.coeff 242 =
      (((((11580554628722280099335225210 * 10 ^ 70 +
        9680742707215584208116815708875786166777399976490210595741888005240635) * 10 ^ 70 +
        1824652800076015624934501312250199276577068236731117988245530370536236) * 10 ^ 70 +
        5040616628751304487232121038981735140809414276281831075591941598175183) * 10 ^ 70 +
        2155065469919678876522012367135233546940798812730608870572328577723280) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (242 - x)) = _
  rw [show 243 = 48 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (243 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (243 + x) *
        remainder4Coefficient0.coeff (243 - (243 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 243 + x
  · rw [recurrence4LeadingSquare_coeff_high (243 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (243 - (243 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_243 :
    recurrence4Scalar0Left.coeff 243 =
      -(((((12906058855688413835540473497 * 10 ^ 70 +
        8976408222402189102878232065463713729189515011606433013307430279498954) * 10 ^ 70 +
        5468547808302864886851888139177256579288624703755034461490435518897595) * 10 ^ 70 +
        7286730636601912216656115695555836714276370700007377944126961424753680) * 10 ^ 70 +
        5476931661979874002686944605194926145332955872953812857095804726279195) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (243 - x)) = _
  rw [show 244 = 49 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (244 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (244 + x) *
        remainder4Coefficient0.coeff (244 - (244 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 244 + x
  · rw [recurrence4LeadingSquare_coeff_high (244 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (244 - (244 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_244 :
    recurrence4Scalar0Left.coeff 244 =
      (((((14128043066072304756264637036 * 10 ^ 70 +
        4219620908555284179219114544189150955521486456586661152665188320344029) * 10 ^ 70 +
        4043374207686102959570405480243582032693472642687145315030541718952833) * 10 ^ 70 +
        1370203778309416977708446777415179195326628045925753995666515977316303) * 10 ^ 70 +
        6226301625529582142632359631222774512497864095785553519554366403260825) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (244 - x)) = _
  rw [show 245 = 50 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (245 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (245 + x) *
        remainder4Coefficient0.coeff (245 - (245 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 245 + x
  · rw [recurrence4LeadingSquare_coeff_high (245 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (245 - (245 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_245 :
    recurrence4Scalar0Left.coeff 245 =
      -(((((15181840582976532496255493130 * 10 ^ 70 +
        5012217348203584373278637579652759700914776960967909863958775396298718) * 10 ^ 70 +
        3722069920991900372726317783383913866532176110222261717348158794628468) * 10 ^ 70 +
        5324564844280683297286027375221767328996077647852083045770027849781840) * 10 ^ 70 +
        7043780861235704967483377299937240684735989316134615286269744262901151) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (245 - x)) = _
  rw [show 246 = 51 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (246 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (246 + x) *
        remainder4Coefficient0.coeff (246 - (246 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 246 + x
  · rw [recurrence4LeadingSquare_coeff_high (246 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (246 - (246 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_246 :
    recurrence4Scalar0Left.coeff 246 =
      (((((16002628731407612931557160838 * 10 ^ 70 +
        5169278782730147186491167550276840466459611253763215441364358703901179) * 10 ^ 70 +
        7446731608087020784176442571138900678287866893138968691844930853173111) * 10 ^ 70 +
        5324009886054697625268646757992998677856519671357922326609304485786228) * 10 ^ 70 +
        4543184415385765093390078098502292120122480728750135429059592558951466) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (246 - x)) = _
  rw [show 247 = 52 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (247 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (247 + x) *
        remainder4Coefficient0.coeff (247 - (247 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 247 + x
  · rw [recurrence4LeadingSquare_coeff_high (247 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (247 - (247 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_247 :
    recurrence4Scalar0Left.coeff 247 =
      -(((((16530061956152068297211618226 * 10 ^ 70 +
        2417342414958732624616822010639208038705589181654127720700368856417137) * 10 ^ 70 +
        3290818138184083871445451574961912239299052865602891727411454019615119) * 10 ^ 70 +
        4883338260018971593354280528142218151398720100860243296594324632009835) * 10 ^ 70 +
        4487726973885206556714152946462129401559992059900850628712122097146714) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (247 - x)) = _
  rw [show 248 = 53 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (248 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (248 + x) *
        remainder4Coefficient0.coeff (248 - (248 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 248 + x
  · rw [recurrence4LeadingSquare_coeff_high (248 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (248 - (248 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_248 :
    recurrence4Scalar0Left.coeff 248 =
      (((((16713188040349340126890591492 * 10 ^ 70 +
        1604119487332726006701310430623990353276783050649107783873828979657620) * 10 ^ 70 +
        3496163048588627119533463116888572452801608143958948495382375494037035) * 10 ^ 70 +
        0725791389310020765478360801936128116630467615131198156370961944955879) * 10 ^ 70 +
        8553265160679387885303646701460942504886145602071482141571066541982513) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (248 - x)) = _
  rw [show 249 = 54 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (249 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (249 + x) *
        remainder4Coefficient0.coeff (249 - (249 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 249 + x
  · rw [recurrence4LeadingSquare_coeff_high (249 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (249 - (249 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_249 :
    recurrence4Scalar0Left.coeff 249 =
      -(((((16515192401144179763528931712 * 10 ^ 70 +
        8499102587049657447989393903896360049798700634054632796182951148658817) * 10 ^ 70 +
        6058790953774755406242411153228347097116425852753661084876056963397772) * 10 ^ 70 +
        1466367634841624196578485249111796065120923953542463350832806788105598) * 10 ^ 70 +
        1222366902095573283879311546723500556971251248993511579185382027481716) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (249 - x)) = _
  rw [show 250 = 55 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (250 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (250 + x) *
        remainder4Coefficient0.coeff (250 - (250 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 250 + x
  · rw [recurrence4LeadingSquare_coeff_high (250 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (250 - (250 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_250 :
    recurrence4Scalar0Left.coeff 250 =
      (((((15917473637075862199224116155 * 10 ^ 70 +
        1631700870941741356727844591157675546234499716537857561310086710651612) * 10 ^ 70 +
        5727468775892540558216762575885668436330068787204334582664797377875009) * 10 ^ 70 +
        9913330717773919141483340310553135704706179473487836598636849833594576) * 10 ^ 70 +
        3833491640090483048894351009354434450968557895048065805338123225780501) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (250 - x)) = _
  rw [show 251 = 56 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (251 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (251 + x) *
        remainder4Coefficient0.coeff (251 - (251 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 251 + x
  · rw [recurrence4LeadingSquare_coeff_high (251 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (251 - (251 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_251 :
    recurrence4Scalar0Left.coeff 251 =
      -(((((14922569866251626903083040757 * 10 ^ 70 +
        7699474525843415323998355056824797642707127010294587623250760664099617) * 10 ^ 70 +
        5730110032546231407303780775815949448766672822538326356710806855218300) * 10 ^ 70 +
        3270570913357983646133303605550045875671391854854442120675339953606871) * 10 ^ 70 +
        4286745492958344872463577320753002987034790955600874111638973548205140) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (251 - x)) = _
  rw [show 252 = 57 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (252 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (252 + x) *
        remainder4Coefficient0.coeff (252 - (252 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 252 + x
  · rw [recurrence4LeadingSquare_coeff_high (252 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (252 - (252 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_252 :
    recurrence4Scalar0Left.coeff 252 =
      (((((13555534798221781938836243375 * 10 ^ 70 +
        2319606292245731174656730504184693375726489293411213359152244856976600) * 10 ^ 70 +
        9917141117744326638755490982918184754570369441309984284482612269879019) * 10 ^ 70 +
        8014162097718748612490379609605097606752816889740312929165862741724600) * 10 ^ 70 +
        3340237441142114267841867202371706194034711131046838901897758096800336) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (252 - x)) = _
  rw [show 253 = 58 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (253 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (253 + x) *
        remainder4Coefficient0.coeff (253 - (253 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 253 + x
  · rw [recurrence4LeadingSquare_coeff_high (253 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (253 - (253 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_253 :
    recurrence4Scalar0Left.coeff 253 =
      -(((((11863500644819088041406101446 * 10 ^ 70 +
        7545030930029521813412586768821790281638804677471792872722451043208319) * 10 ^ 70 +
        1010926047388902282867351573262637648821754035244719795506934665385297) * 10 ^ 70 +
        4411984847303809112756287671607328599173981898683458427202407173695792) * 10 ^ 70 +
        8363686074456813756586567756109334911916377400022105791033669096360940) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (253 - x)) = _
  rw [show 254 = 59 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (254 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (254 + x) *
        remainder4Coefficient0.coeff (254 - (254 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 254 + x
  · rw [recurrence4LeadingSquare_coeff_high (254 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (254 - (254 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_254 :
    recurrence4Scalar0Left.coeff 254 =
      (((((9913348160918607423032588433 * 10 ^ 70 +
        5622755748692965390953576934368872581959423478897337222961299162870567) * 10 ^ 70 +
        6204657102781996074287220582702248396499794779136592905416433949327767) * 10 ^ 70 +
        6639919143286062312141819618095743241628027090351447437781595747187658) * 10 ^ 70 +
        0309605543954031458800145547126680349076477129020188699089836279644353) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (254 - x)) = _
  rw [show 255 = 60 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (255 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (255 + x) *
        remainder4Coefficient0.coeff (255 - (255 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 255 + x
  · rw [recurrence4LeadingSquare_coeff_high (255 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (255 - (255 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_255 :
    recurrence4Scalar0Left.coeff 255 =
      -(((((7787610494595371007913890288 * 10 ^ 70 +
        4497415257052241284331231985712413456328232826005248661737476076596189) * 10 ^ 70 +
        3103907097311178702449879161298915648622631625298185706608130200842693) * 10 ^ 70 +
        5559224284391909973731141226618920446537469050120094543472156722487991) * 10 ^ 70 +
        8539396694473124367674419640370734159351249119921410919281491564296156) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (255 - x)) = _
  rw [show 256 = 61 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (256 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (256 + x) *
        remainder4Coefficient0.coeff (256 - (256 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 256 + x
  · rw [recurrence4LeadingSquare_coeff_high (256 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (256 - (256 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_256 :
    recurrence4Scalar0Left.coeff 256 =
      (((((5578940148717378917058065060 * 10 ^ 70 +
        0735728478771261252537528490395295837378067305222586961761675206065450) * 10 ^ 70 +
        1230848641222936100563681968985056633160672490145215536456226724949379) * 10 ^ 70 +
        1065623876900321769215504952912907428280017812534399009850918820683166) * 10 ^ 70 +
        5793203723851970603316405631560920160014279558850927990504757036870240) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (256 - x)) = _
  rw [show 257 = 62 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (257 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (257 + x) *
        remainder4Coefficient0.coeff (257 - (257 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 257 + x
  · rw [recurrence4LeadingSquare_coeff_high (257 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (257 - (257 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_257 :
    recurrence4Scalar0Left.coeff 257 =
      -(((((3383639170953661982122788372 * 10 ^ 70 +
        0166969235674608723673336590376664738816252407435075545377974262425957) * 10 ^ 70 +
        1657839706814374845160443316138936964098955783379979222198344299945443) * 10 ^ 70 +
        0352993084381826860800327033510603899146741850809267505143563343798310) * 10 ^ 70 +
        8524661843927807102175245019272729445866366407685639764390232426387759) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (257 - x)) = _
  rw [show 258 = 63 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (258 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (258 + x) *
        remainder4Coefficient0.coeff (258 - (258 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 258 + x
  · rw [recurrence4LeadingSquare_coeff_high (258 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (258 - (258 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_258 :
    recurrence4Scalar0Left.coeff 258 =
      (((((1294867100893988569226995443 * 10 ^ 70 +
        7618220233121649099718353637078626370819572042403557054365773730390383) * 10 ^ 70 +
        5108583560228209161494186966958002557834041414210933443931872442017302) * 10 ^ 70 +
        1697168920362543996995485053011506438102979801189290194591934310221290) * 10 ^ 70 +
        2582281188807738851983249685618135582664494979222100399359065774389850) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (258 - x)) = _
  rw [show 259 = 64 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (259 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (259 + x) *
        remainder4Coefficient0.coeff (259 - (259 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 259 + x
  · rw [recurrence4LeadingSquare_coeff_high (259 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (259 - (259 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_259 :
    recurrence4Scalar0Left.coeff 259 =
      (((((603817803982169316584759180 * 10 ^ 70 +
        6653358450888130650742959132345386096007307632179729492327755368819996) * 10 ^ 70 +
        9076536544110105825023843940473357233821870535692755435999081425588913) * 10 ^ 70 +
        1946589767759983043170292150551660614289739293288376545609134723893270) * 10 ^ 70 +
        3634451845523675876261403673141624021149116648082735575254277636541168) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (259 - x)) = _
  rw [show 260 = 65 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (260 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (260 + x) *
        remainder4Coefficient0.coeff (260 - (260 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 260 + x
  · rw [recurrence4LeadingSquare_coeff_high (260 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (260 - (260 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_260 :
    recurrence4Scalar0Left.coeff 260 =
      -(((((2243967445488028813662489361 * 10 ^ 70 +
        8341336096655346655031756841911601275732546025521645864622997792688045) * 10 ^ 70 +
        5816415776270335075278971659531933589300640759587288061810459530669934) * 10 ^ 70 +
        2630894057177601660876800124469563160819217513310980469353284388254135) * 10 ^ 70 +
        4279845329939779491908203247976640514645397097183492593553534460695305) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (260 - x)) = _
  rw [show 261 = 66 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (261 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (261 + x) *
        remainder4Coefficient0.coeff (261 - (261 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 261 + x
  · rw [recurrence4LeadingSquare_coeff_high (261 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (261 - (261 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_261 :
    recurrence4Scalar0Left.coeff 261 =
      (((((3576299793829200752809945727 * 10 ^ 70 +
        0512189283434538670919300127684588476995055664362802182570566981350448) * 10 ^ 70 +
        3506243150184641409443480238325446562565667196081539304258828200572281) * 10 ^ 70 +
        2182499024116990836306373496432949651002341216386370541823924196538521) * 10 ^ 70 +
        0714641587611312321712721583808155513695449532197069294923301238502261) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (261 - x)) = _
  rw [show 262 = 67 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (262 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (262 + x) *
        remainder4Coefficient0.coeff (262 - (262 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 262 + x
  · rw [recurrence4LeadingSquare_coeff_high (262 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (262 - (262 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_262 :
    recurrence4Scalar0Left.coeff 262 =
      -(((((4572970779157274849686958576 * 10 ^ 70 +
        8973901970970060396471197521263639443988209750899887663394177723396190) * 10 ^ 70 +
        1056867285545934012282921381310496342982472511490133196933082447798203) * 10 ^ 70 +
        8276584657794519254216105541768822863411633637262226206624154414911821) * 10 ^ 70 +
        0607452986320927760173561710785425795470263829604544144720627124820843) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (262 - x)) = _
  rw [show 263 = 68 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (263 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (263 + x) *
        remainder4Coefficient0.coeff (263 - (263 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 263 + x
  · rw [recurrence4LeadingSquare_coeff_high (263 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (263 - (263 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_263 :
    recurrence4Scalar0Left.coeff 263 =
      (((((5227937215371221514290253012 * 10 ^ 70 +
        3142933484633197985808495353855159533873345432573346042417102929112606) * 10 ^ 70 +
        3450294092708382407214497095532845241543242543178631811395576151128017) * 10 ^ 70 +
        9156069358091794786639441835681645766394753600844167414889303963040598) * 10 ^ 70 +
        4830267890730253863093025927794282332935326769905745963202274960320064) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (263 - x)) = _
  rw [show 264 = 69 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (264 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (264 + x) *
        remainder4Coefficient0.coeff (264 - (264 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 264 + x
  · rw [recurrence4LeadingSquare_coeff_high (264 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (264 - (264 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_264 :
    recurrence4Scalar0Left.coeff 264 =
      -(((((5555497397319278569777167707 * 10 ^ 70 +
        1536903805513104903808610067248502811660274101787505069810169681586621) * 10 ^ 70 +
        6632634303974922730825083070409434824644198820744113093943950207522584) * 10 ^ 70 +
        3772704466107393557607659485809323862993213022207334529022037617216618) * 10 ^ 70 +
        7361036517282128704823981880484740008543475249505909959371863441062762) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (264 - x)) = _
  rw [show 265 = 70 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (265 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (265 + x) *
        remainder4Coefficient0.coeff (265 - (265 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 265 + x
  · rw [recurrence4LeadingSquare_coeff_high (265 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (265 - (265 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_265 :
    recurrence4Scalar0Left.coeff 265 =
      (((((5587284954849309418072616346 * 10 ^ 70 +
        5481804645507292487518874800350947742586346373317871718460765485139456) * 10 ^ 70 +
        2843403743193400292646112286568314342391242464977069854799116065782597) * 10 ^ 70 +
        7419851464154213405270063161409864576773730158378973889737398126786771) * 10 ^ 70 +
        1244513766175006061150200106434604227352579949830701056681994974081990) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (265 - x)) = _
  rw [show 266 = 71 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (266 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (266 + x) *
        remainder4Coefficient0.coeff (266 - (266 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 266 + x
  · rw [recurrence4LeadingSquare_coeff_high (266 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (266 - (266 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_266 :
    recurrence4Scalar0Left.coeff 266 =
      -(((((5368134507245224953649395329 * 10 ^ 70 +
        3879944598348241339820860867474030227516527271828087799400156806867017) * 10 ^ 70 +
        2264734589232501437158163310767868341896423533909603912451748191455051) * 10 ^ 70 +
        7229367135822559834691440718451280721073755846338041828725821816544110) * 10 ^ 70 +
        0969694654756896994428792352560120329152709648157259079480253896144743) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (266 - x)) = _
  rw [show 267 = 72 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (267 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (267 + x) *
        remainder4Coefficient0.coeff (267 - (267 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 267 + x
  · rw [recurrence4LeadingSquare_coeff_high (267 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (267 - (267 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_267 :
    recurrence4Scalar0Left.coeff 267 =
      (((((4951319437974120770610127333 * 10 ^ 70 +
        7680703976498962480153507599229082775297261421558251748980520376290493) * 10 ^ 70 +
        1590694762319810234401123757770771415912201007218346746978208118644013) * 10 ^ 70 +
        6292561373908223552670496708781659215208753631328977245024708651164288) * 10 ^ 70 +
        3549007067308817461267831837335924748607058402217899800796429970232709) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (267 - x)) = _
  rw [show 268 = 73 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4A0_coeff_high (268 - x) (by
    omega)]
  norm_num

private theorem recurrence4Scalar0Left_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence4LeadingSquare.coeff (268 + x) *
        remainder4Coefficient0.coeff (268 - (268 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : 328 < 268 + x
  · rw [recurrence4LeadingSquare_coeff_high (268 + x) hleft]
    norm_num
  · rw [recurrence4A0_coeff_low
      (268 - (268 + x)) (by omega)]
    norm_num

theorem recurrence4Scalar0Left_coeff_268 :
    recurrence4Scalar0Left.coeff 268 =
      -(((((4393677384017329703642390131 * 10 ^ 70 +
        4344634861317756300533409659056370302038116722891025708766717471582009) * 10 ^ 70 +
        2073467853088173560543493385977404237255192543831043072466359630598800) * 10 ^ 70 +
        1272352976832891989107217054931660626841045900348158946939734661276841) * 10 ^ 70 +
        8179111144037297354635756352697140448109846267526106880732338690284228) : ℚ) := by
  unfold recurrence4Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    recurrence4LeadingSquare.coeff x * remainder4Coefficient0.coeff (268 - x)) = _
  rw [show 269 = 74 +
    195 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 32 +
      35 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 35 = 32 +
      3 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 3 = 2 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Left_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Left_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
