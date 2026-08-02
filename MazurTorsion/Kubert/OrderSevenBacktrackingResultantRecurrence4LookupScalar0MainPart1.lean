/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/

open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_1
  recurrence4B0_coeff_10
  recurrence4B0_coeff_100
  recurrence4B0_coeff_101
  recurrence4B0_coeff_102
  recurrence4B0_coeff_103
  recurrence4B0_coeff_104
  recurrence4B0_coeff_105
  recurrence4B0_coeff_106
  recurrence4B0_coeff_107
  recurrence4B0_coeff_108
  recurrence4B0_coeff_109
  recurrence4B0_coeff_11
  recurrence4B0_coeff_110
  recurrence4B0_coeff_111
  recurrence4B0_coeff_112
  recurrence4B0_coeff_113
  recurrence4B0_coeff_114
  recurrence4B0_coeff_115
  recurrence4B0_coeff_116
  recurrence4B0_coeff_117
  recurrence4B0_coeff_118
  recurrence4B0_coeff_119
  recurrence4B0_coeff_12
  recurrence4B0_coeff_120
  recurrence4B0_coeff_121
  recurrence4B0_coeff_122
  recurrence4B0_coeff_123
  recurrence4B0_coeff_124
  recurrence4B0_coeff_125
  recurrence4B0_coeff_126
  recurrence4B0_coeff_127
  recurrence4B0_coeff_128
  recurrence4B0_coeff_129
  recurrence4B0_coeff_13
  recurrence4B0_coeff_130
  recurrence4B0_coeff_131
  recurrence4B0_coeff_132
  recurrence4B0_coeff_133
  recurrence4B0_coeff_134
  recurrence4B0_coeff_135
  recurrence4B0_coeff_136
  recurrence4B0_coeff_137
  recurrence4B0_coeff_138
  recurrence4B0_coeff_139
  recurrence4B0_coeff_14
  recurrence4B0_coeff_140
  recurrence4B0_coeff_141
  recurrence4B0_coeff_142
  recurrence4B0_coeff_143
  recurrence4B0_coeff_144
  recurrence4B0_coeff_145
  recurrence4B0_coeff_146
  recurrence4B0_coeff_147
  recurrence4B0_coeff_148
  recurrence4B0_coeff_149
  recurrence4B0_coeff_15
  recurrence4B0_coeff_150
  recurrence4B0_coeff_151
  recurrence4B0_coeff_152
  recurrence4B0_coeff_153
  recurrence4B0_coeff_154
  recurrence4B0_coeff_155
  recurrence4B0_coeff_156

attribute [local simp]
  recurrence4B0_coeff_157
  recurrence4B0_coeff_158
  recurrence4B0_coeff_159
  recurrence4B0_coeff_16
  recurrence4B0_coeff_160
  recurrence4B0_coeff_161
  recurrence4B0_coeff_162
  recurrence4B0_coeff_163
  recurrence4B0_coeff_164
  recurrence4B0_coeff_165
  recurrence4B0_coeff_166
  recurrence4B0_coeff_167
  recurrence4B0_coeff_168
  recurrence4B0_coeff_169
  recurrence4B0_coeff_17
  recurrence4B0_coeff_170
  recurrence4B0_coeff_171
  recurrence4B0_coeff_172
  recurrence4B0_coeff_173
  recurrence4B0_coeff_174
  recurrence4B0_coeff_175
  recurrence4B0_coeff_176
  recurrence4B0_coeff_18
  recurrence4B0_coeff_19
  recurrence4B0_coeff_2
  recurrence4B0_coeff_20
  recurrence4B0_coeff_21
  recurrence4B0_coeff_22
  recurrence4B0_coeff_23
  recurrence4B0_coeff_24
  recurrence4B0_coeff_25
  recurrence4B0_coeff_26
  recurrence4B0_coeff_27
  recurrence4B0_coeff_28
  recurrence4B0_coeff_29
  recurrence4B0_coeff_3
  recurrence4B0_coeff_30
  recurrence4B0_coeff_31
  recurrence4B0_coeff_32
  recurrence4B0_coeff_33
  recurrence4B0_coeff_34
  recurrence4B0_coeff_35
  recurrence4B0_coeff_36
  recurrence4B0_coeff_37
  recurrence4B0_coeff_38
  recurrence4B0_coeff_39
  recurrence4B0_coeff_4
  recurrence4B0_coeff_40
  recurrence4B0_coeff_41
  recurrence4B0_coeff_42
  recurrence4B0_coeff_43
  recurrence4B0_coeff_44
  recurrence4B0_coeff_45
  recurrence4B0_coeff_46
  recurrence4B0_coeff_47
  recurrence4B0_coeff_48
  recurrence4B0_coeff_49
  recurrence4B0_coeff_5
  recurrence4B0_coeff_50
  recurrence4B0_coeff_51
  recurrence4B0_coeff_52
  recurrence4B0_coeff_53
  recurrence4B0_coeff_54
  recurrence4B0_coeff_55

attribute [local simp]
  recurrence4B0_coeff_56
  recurrence4B0_coeff_57
  recurrence4B0_coeff_58
  recurrence4B0_coeff_59
  recurrence4B0_coeff_6
  recurrence4B0_coeff_60
  recurrence4B0_coeff_61
  recurrence4B0_coeff_62
  recurrence4B0_coeff_63
  recurrence4B0_coeff_64
  recurrence4B0_coeff_65
  recurrence4B0_coeff_66
  recurrence4B0_coeff_67
  recurrence4B0_coeff_68
  recurrence4B0_coeff_69
  recurrence4B0_coeff_7
  recurrence4B0_coeff_70
  recurrence4B0_coeff_71
  recurrence4B0_coeff_72
  recurrence4B0_coeff_73
  recurrence4B0_coeff_74
  recurrence4B0_coeff_75
  recurrence4B0_coeff_76
  recurrence4B0_coeff_77
  recurrence4B0_coeff_78
  recurrence4B0_coeff_79
  recurrence4B0_coeff_8
  recurrence4B0_coeff_80
  recurrence4B0_coeff_81
  recurrence4B0_coeff_82
  recurrence4B0_coeff_83
  recurrence4B0_coeff_84
  recurrence4B0_coeff_85
  recurrence4B0_coeff_86
  recurrence4B0_coeff_87
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_9
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
  recurrence4QuotientConstant_coeff_0
  recurrence4QuotientConstant_coeff_1
  recurrence4QuotientConstant_coeff_10
  recurrence4QuotientConstant_coeff_100
  recurrence4QuotientConstant_coeff_101
  recurrence4QuotientConstant_coeff_102
  recurrence4QuotientConstant_coeff_103
  recurrence4QuotientConstant_coeff_104
  recurrence4QuotientConstant_coeff_105
  recurrence4QuotientConstant_coeff_106
  recurrence4QuotientConstant_coeff_107
  recurrence4QuotientConstant_coeff_108
  recurrence4QuotientConstant_coeff_109
  recurrence4QuotientConstant_coeff_11
  recurrence4QuotientConstant_coeff_110
  recurrence4QuotientConstant_coeff_111

attribute [local simp]
  recurrence4QuotientConstant_coeff_112
  recurrence4QuotientConstant_coeff_113
  recurrence4QuotientConstant_coeff_114
  recurrence4QuotientConstant_coeff_115
  recurrence4QuotientConstant_coeff_116
  recurrence4QuotientConstant_coeff_117
  recurrence4QuotientConstant_coeff_118
  recurrence4QuotientConstant_coeff_119
  recurrence4QuotientConstant_coeff_12
  recurrence4QuotientConstant_coeff_120
  recurrence4QuotientConstant_coeff_121
  recurrence4QuotientConstant_coeff_122
  recurrence4QuotientConstant_coeff_123
  recurrence4QuotientConstant_coeff_124
  recurrence4QuotientConstant_coeff_125
  recurrence4QuotientConstant_coeff_126
  recurrence4QuotientConstant_coeff_127
  recurrence4QuotientConstant_coeff_128
  recurrence4QuotientConstant_coeff_129
  recurrence4QuotientConstant_coeff_13
  recurrence4QuotientConstant_coeff_130
  recurrence4QuotientConstant_coeff_131
  recurrence4QuotientConstant_coeff_132
  recurrence4QuotientConstant_coeff_133
  recurrence4QuotientConstant_coeff_134
  recurrence4QuotientConstant_coeff_135
  recurrence4QuotientConstant_coeff_136
  recurrence4QuotientConstant_coeff_137
  recurrence4QuotientConstant_coeff_138
  recurrence4QuotientConstant_coeff_139
  recurrence4QuotientConstant_coeff_14
  recurrence4QuotientConstant_coeff_140
  recurrence4QuotientConstant_coeff_141
  recurrence4QuotientConstant_coeff_142
  recurrence4QuotientConstant_coeff_143
  recurrence4QuotientConstant_coeff_144
  recurrence4QuotientConstant_coeff_145
  recurrence4QuotientConstant_coeff_146
  recurrence4QuotientConstant_coeff_147
  recurrence4QuotientConstant_coeff_148
  recurrence4QuotientConstant_coeff_149
  recurrence4QuotientConstant_coeff_15
  recurrence4QuotientConstant_coeff_150
  recurrence4QuotientConstant_coeff_151
  recurrence4QuotientConstant_coeff_152
  recurrence4QuotientConstant_coeff_153
  recurrence4QuotientConstant_coeff_154
  recurrence4QuotientConstant_coeff_155
  recurrence4QuotientConstant_coeff_156
  recurrence4QuotientConstant_coeff_157
  recurrence4QuotientConstant_coeff_158
  recurrence4QuotientConstant_coeff_159
  recurrence4QuotientConstant_coeff_16
  recurrence4QuotientConstant_coeff_160
  recurrence4QuotientConstant_coeff_161
  recurrence4QuotientConstant_coeff_162
  recurrence4QuotientConstant_coeff_163
  recurrence4QuotientConstant_coeff_164
  recurrence4QuotientConstant_coeff_165
  recurrence4QuotientConstant_coeff_166
  recurrence4QuotientConstant_coeff_167
  recurrence4QuotientConstant_coeff_168
  recurrence4QuotientConstant_coeff_169
  recurrence4QuotientConstant_coeff_17

attribute [local simp]
  recurrence4QuotientConstant_coeff_170
  recurrence4QuotientConstant_coeff_171
  recurrence4QuotientConstant_coeff_172
  recurrence4QuotientConstant_coeff_173
  recurrence4QuotientConstant_coeff_174
  recurrence4QuotientConstant_coeff_175
  recurrence4QuotientConstant_coeff_176
  recurrence4QuotientConstant_coeff_177
  recurrence4QuotientConstant_coeff_178
  recurrence4QuotientConstant_coeff_179
  recurrence4QuotientConstant_coeff_18
  recurrence4QuotientConstant_coeff_180
  recurrence4QuotientConstant_coeff_181
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186
  recurrence4QuotientConstant_coeff_187
  recurrence4QuotientConstant_coeff_188
  recurrence4QuotientConstant_coeff_189
  recurrence4QuotientConstant_coeff_19
  recurrence4QuotientConstant_coeff_190
  recurrence4QuotientConstant_coeff_191
  recurrence4QuotientConstant_coeff_192
  recurrence4QuotientConstant_coeff_193
  recurrence4QuotientConstant_coeff_194
  recurrence4QuotientConstant_coeff_195
  recurrence4QuotientConstant_coeff_196
  recurrence4QuotientConstant_coeff_197
  recurrence4QuotientConstant_coeff_198
  recurrence4QuotientConstant_coeff_199
  recurrence4QuotientConstant_coeff_2
  recurrence4QuotientConstant_coeff_20
  recurrence4QuotientConstant_coeff_200
  recurrence4QuotientConstant_coeff_201
  recurrence4QuotientConstant_coeff_202
  recurrence4QuotientConstant_coeff_203
  recurrence4QuotientConstant_coeff_204
  recurrence4QuotientConstant_coeff_205
  recurrence4QuotientConstant_coeff_206
  recurrence4QuotientConstant_coeff_207
  recurrence4QuotientConstant_coeff_208
  recurrence4QuotientConstant_coeff_209
  recurrence4QuotientConstant_coeff_21
  recurrence4QuotientConstant_coeff_210
  recurrence4QuotientConstant_coeff_211
  recurrence4QuotientConstant_coeff_212
  recurrence4QuotientConstant_coeff_213
  recurrence4QuotientConstant_coeff_214
  recurrence4QuotientConstant_coeff_215
  recurrence4QuotientConstant_coeff_216
  recurrence4QuotientConstant_coeff_217
  recurrence4QuotientConstant_coeff_218
  recurrence4QuotientConstant_coeff_219
  recurrence4QuotientConstant_coeff_22
  recurrence4QuotientConstant_coeff_220
  recurrence4QuotientConstant_coeff_221
  recurrence4QuotientConstant_coeff_222
  recurrence4QuotientConstant_coeff_223
  recurrence4QuotientConstant_coeff_224
  recurrence4QuotientConstant_coeff_225
  recurrence4QuotientConstant_coeff_226
  recurrence4QuotientConstant_coeff_227

attribute [local simp]
  recurrence4QuotientConstant_coeff_228
  recurrence4QuotientConstant_coeff_229
  recurrence4QuotientConstant_coeff_23
  recurrence4QuotientConstant_coeff_230
  recurrence4QuotientConstant_coeff_231
  recurrence4QuotientConstant_coeff_232
  recurrence4QuotientConstant_coeff_233
  recurrence4QuotientConstant_coeff_234
  recurrence4QuotientConstant_coeff_235
  recurrence4QuotientConstant_coeff_236
  recurrence4QuotientConstant_coeff_237
  recurrence4QuotientConstant_coeff_238
  recurrence4QuotientConstant_coeff_239
  recurrence4QuotientConstant_coeff_24
  recurrence4QuotientConstant_coeff_240
  recurrence4QuotientConstant_coeff_241
  recurrence4QuotientConstant_coeff_242
  recurrence4QuotientConstant_coeff_243
  recurrence4QuotientConstant_coeff_244
  recurrence4QuotientConstant_coeff_245
  recurrence4QuotientConstant_coeff_246
  recurrence4QuotientConstant_coeff_247
  recurrence4QuotientConstant_coeff_248
  recurrence4QuotientConstant_coeff_249
  recurrence4QuotientConstant_coeff_25
  recurrence4QuotientConstant_coeff_250
  recurrence4QuotientConstant_coeff_251
  recurrence4QuotientConstant_coeff_252
  recurrence4QuotientConstant_coeff_253
  recurrence4QuotientConstant_coeff_254
  recurrence4QuotientConstant_coeff_255
  recurrence4QuotientConstant_coeff_256
  recurrence4QuotientConstant_coeff_257
  recurrence4QuotientConstant_coeff_258
  recurrence4QuotientConstant_coeff_259
  recurrence4QuotientConstant_coeff_26
  recurrence4QuotientConstant_coeff_260
  recurrence4QuotientConstant_coeff_261
  recurrence4QuotientConstant_coeff_262
  recurrence4QuotientConstant_coeff_263
  recurrence4QuotientConstant_coeff_264
  recurrence4QuotientConstant_coeff_265
  recurrence4QuotientConstant_coeff_266
  recurrence4QuotientConstant_coeff_267
  recurrence4QuotientConstant_coeff_268
  recurrence4QuotientConstant_coeff_269
  recurrence4QuotientConstant_coeff_27
  recurrence4QuotientConstant_coeff_270
  recurrence4QuotientConstant_coeff_271
  recurrence4QuotientConstant_coeff_272
  recurrence4QuotientConstant_coeff_273
  recurrence4QuotientConstant_coeff_274
  recurrence4QuotientConstant_coeff_275
  recurrence4QuotientConstant_coeff_28
  recurrence4QuotientConstant_coeff_29
  recurrence4QuotientConstant_coeff_3
  recurrence4QuotientConstant_coeff_30
  recurrence4QuotientConstant_coeff_31
  recurrence4QuotientConstant_coeff_32
  recurrence4QuotientConstant_coeff_33
  recurrence4QuotientConstant_coeff_34
  recurrence4QuotientConstant_coeff_35
  recurrence4QuotientConstant_coeff_36
  recurrence4QuotientConstant_coeff_37

attribute [local simp]
  recurrence4QuotientConstant_coeff_38
  recurrence4QuotientConstant_coeff_39
  recurrence4QuotientConstant_coeff_4
  recurrence4QuotientConstant_coeff_40
  recurrence4QuotientConstant_coeff_41
  recurrence4QuotientConstant_coeff_42
  recurrence4QuotientConstant_coeff_43
  recurrence4QuotientConstant_coeff_44
  recurrence4QuotientConstant_coeff_45
  recurrence4QuotientConstant_coeff_46
  recurrence4QuotientConstant_coeff_47
  recurrence4QuotientConstant_coeff_48
  recurrence4QuotientConstant_coeff_49
  recurrence4QuotientConstant_coeff_5
  recurrence4QuotientConstant_coeff_50
  recurrence4QuotientConstant_coeff_51
  recurrence4QuotientConstant_coeff_52
  recurrence4QuotientConstant_coeff_53
  recurrence4QuotientConstant_coeff_54
  recurrence4QuotientConstant_coeff_55
  recurrence4QuotientConstant_coeff_56
  recurrence4QuotientConstant_coeff_57
  recurrence4QuotientConstant_coeff_58
  recurrence4QuotientConstant_coeff_59
  recurrence4QuotientConstant_coeff_6
  recurrence4QuotientConstant_coeff_60
  recurrence4QuotientConstant_coeff_61
  recurrence4QuotientConstant_coeff_62
  recurrence4QuotientConstant_coeff_63
  recurrence4QuotientConstant_coeff_64
  recurrence4QuotientConstant_coeff_65
  recurrence4QuotientConstant_coeff_66
  recurrence4QuotientConstant_coeff_67
  recurrence4QuotientConstant_coeff_68
  recurrence4QuotientConstant_coeff_69
  recurrence4QuotientConstant_coeff_7
  recurrence4QuotientConstant_coeff_70
  recurrence4QuotientConstant_coeff_71
  recurrence4QuotientConstant_coeff_72
  recurrence4QuotientConstant_coeff_73
  recurrence4QuotientConstant_coeff_74
  recurrence4QuotientConstant_coeff_75
  recurrence4QuotientConstant_coeff_76
  recurrence4QuotientConstant_coeff_77
  recurrence4QuotientConstant_coeff_78
  recurrence4QuotientConstant_coeff_79
  recurrence4QuotientConstant_coeff_8
  recurrence4QuotientConstant_coeff_80
  recurrence4QuotientConstant_coeff_81
  recurrence4QuotientConstant_coeff_82
  recurrence4QuotientConstant_coeff_83
  recurrence4QuotientConstant_coeff_84
  recurrence4QuotientConstant_coeff_85
  recurrence4QuotientConstant_coeff_86
  recurrence4QuotientConstant_coeff_87
  recurrence4QuotientConstant_coeff_88
  recurrence4QuotientConstant_coeff_89
  recurrence4QuotientConstant_coeff_9
  recurrence4QuotientConstant_coeff_90
  recurrence4QuotientConstant_coeff_91
  recurrence4QuotientConstant_coeff_92
  recurrence4QuotientConstant_coeff_93
  recurrence4QuotientConstant_coeff_94
  recurrence4QuotientConstant_coeff_95

attribute [local simp]
  recurrence4QuotientConstant_coeff_96
  recurrence4QuotientConstant_coeff_97
  recurrence4QuotientConstant_coeff_98
  recurrence4QuotientConstant_coeff_99

private theorem recurrence4Scalar0Main_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (171 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_171 :
    recurrence4Scalar0Main.coeff 171 =
      -(((((211064879 * 10 ^ 70 +
        2884282770989700612659821230660045042926537381599124634139719947714478) * 10 ^ 70 +
        5299405183808381832602182864295884771237084758368131171778525916641680) * 10 ^ 70 +
        8727281904589959421568778139740170187035195363591363811963068766170422) * 10 ^ 70 +
        9836395457633544154077903351741971625094807000896728286546932899797592) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (171 - x)) = _
  rw [show 172 = 1 +
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
    rw [show 11 = 11 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (172 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_172 :
    recurrence4Scalar0Main.coeff 172 =
      (((((664068068 * 10 ^ 70 +
        4017633262548879399566535455347950287816586733848769506259572590158313) * 10 ^ 70 +
        8966354000838134601536439077036271476518480403306315621457917182422576) * 10 ^ 70 +
        1721431335588456187193550840608718687591295307809100720777778823636965) * 10 ^ 70 +
        5867972745931681416326752020751811389661084144942881544740457932105569) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (172 - x)) = _
  rw [show 173 = 1 +
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
    rw [show 12 = 12 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (173 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_173 :
    recurrence4Scalar0Main.coeff 173 =
      -(((((2057929878 * 10 ^ 70 +
        2713453052466889376414156198837929495271046610315618359792464151887586) * 10 ^ 70 +
        1516700681261110340413107176863302479529415940891620317583565902111971) * 10 ^ 70 +
        4741361025878151941230467013964541237160662366271457053930276819071663) * 10 ^ 70 +
        2710680092143219145665489394393298459561567586365963555797331780344191) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (173 - x)) = _
  rw [show 174 = 1 +
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
    rw [show 13 = 13 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (174 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_174 :
    recurrence4Scalar0Main.coeff 174 =
      (((((6281946871 * 10 ^ 70 +
        6139020680870891580834914470025857428421685265136752649099958513848145) * 10 ^ 70 +
        8054665251944864183672135097908871493332968666042509969004549017806102) * 10 ^ 70 +
        8353161230115490153335789192952528020831820481503145765142868803658564) * 10 ^ 70 +
        4501013135326684081860456513437326283990171151176470630086454876506904) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (174 - x)) = _
  rw [show 175 = 1 +
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
    rw [show 14 = 14 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (175 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_175 :
    recurrence4Scalar0Main.coeff 175 =
      -(((((18889793893 * 10 ^ 70 +
        1494022126917743533287475712001402479927857294414669475507553756715491) * 10 ^ 70 +
        5281051298851745489455963178994587711676739474197441841844356232767445) * 10 ^ 70 +
        4884845167332668985990830425700201921648103951477181437667959474443510) * 10 ^ 70 +
        0539701187676484752506209045444925360774370893577952102204423148639003) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (175 - x)) = _
  rw [show 176 = 1 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (176 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar0Main_coeff_176 :
    recurrence4Scalar0Main.coeff 176 =
      (((((55956717297 * 10 ^ 70 +
        7285343159511044347885761222389740166851075455579808748738847248401676) * 10 ^ 70 +
        8392013590377043804821208239561704492231493652005476693926733480656544) * 10 ^ 70 +
        1474299288125640065669868644549316579034825651109228353405311542535644) * 10 ^ 70 +
        2010840243212565279948336413889749045303568441338099609150394641461343) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (176 - x)) = _
  rw [show 177 = 1 +
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
    rw [show 16 = 16 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (177 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (177 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_177 :
    recurrence4Scalar0Main.coeff 177 =
      -(((((163301918716 * 10 ^ 70 +
        6931083559098371004793541775895869922874128740694680151876856972396696) * 10 ^ 70 +
        5966864994257460578785710478103879633540389196217916078490832313515119) * 10 ^ 70 +
        1793017809744602849447975112744355378826347032304993306826902204364180) * 10 ^ 70 +
        3676365848772275618759562928579606309375049514237592813107635645074884) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (177 - x)) = _
  rw [show 178 = 1 +
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
  rw [recurrence4Scalar0Main_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (178 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (178 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_178 :
    recurrence4Scalar0Main.coeff 178 =
      (((((469532471402 * 10 ^ 70 +
        2551045056302050521331923867829592835303350981795245905715247704193145) * 10 ^ 70 +
        1703170115187779321904859306092665539613790891596119134412754339516592) * 10 ^ 70 +
        8995118719409074830037371548771941025111825540209514321751377600091380) * 10 ^ 70 +
        9217193722395576455859271766045258477495851131461165282276883480382217) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (178 - x)) = _
  rw [show 179 = 1 +
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
    rw [show 18 = 16 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (179 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (179 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_179 :
    recurrence4Scalar0Main.coeff 179 =
      -(((((1330135070179 * 10 ^ 70 +
        7407732705555773746176089728420947953412188470810839594446951913352629) * 10 ^ 70 +
        8870169880694655136410748030897986642438063116626212606159701031979561) * 10 ^ 70 +
        5521914122509207730025571700685044467148091337333187283482390613879511) * 10 ^ 70 +
        4699694705526670689029850311142130614793147689751890281496732134243337) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (179 - x)) = _
  rw [show 180 = 1 +
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
    rw [show 19 = 16 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (180 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (180 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_180 :
    recurrence4Scalar0Main.coeff 180 =
      (((((3712798327936 * 10 ^ 70 +
        4714855909957873925141471779552320319077821863878403520688622185856576) * 10 ^ 70 +
        5686043860858010629663474949222939608493806663341754256335732462611076) * 10 ^ 70 +
        2137882929021767663998621402938877267045848497046959987738963026923485) * 10 ^ 70 +
        0214094916229743744327661921360116653078820629113150559995926396601794) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (180 - x)) = _
  rw [show 181 = 1 +
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
    rw [show 20 = 16 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (181 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (181 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_181 :
    recurrence4Scalar0Main.coeff 181 =
      -(((((10211780644685 * 10 ^ 70 +
        2532955837970227602903558918058158121205838188049945938473034707766476) * 10 ^ 70 +
        1718024697476316006265780207558320850898722646173637908962178965380155) * 10 ^ 70 +
        9744799415484447126945366877966807292405877043535617401498742424088807) * 10 ^ 70 +
        5349496516025688696572249317545466193036573188517221818348870423878632) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (181 - x)) = _
  rw [show 182 = 1 +
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
    rw [show 21 = 16 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (182 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (182 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_182 :
    recurrence4Scalar0Main.coeff 182 =
      (((((27676703668705 * 10 ^ 70 +
        9673144766593104522454515294185109213327563079648496433372765379186710) * 10 ^ 70 +
        4068905692854407137209071523061912419273513630519631307401561105226712) * 10 ^ 70 +
        9766022891667175867373917547720493421420002432427742402020503077083777) * 10 ^ 70 +
        2641881517047474148835963294495282818913257628518654245684972659399834) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (182 - x)) = _
  rw [show 183 = 1 +
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
    rw [show 22 = 16 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (183 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (183 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_183 :
    recurrence4Scalar0Main.coeff 183 =
      -(((((73919251594052 * 10 ^ 70 +
        6240248482203528222199573574709789190136701875759902205905185684895119) * 10 ^ 70 +
        6670140267795191569155126129549094470803503862440246883716491498530502) * 10 ^ 70 +
        6517646137273666891488940393465802825651289232519928775164180050665992) * 10 ^ 70 +
        3200214504895529924649763465660656695936791709859842044962329934888113) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (183 - x)) = _
  rw [show 184 = 1 +
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
    rw [show 23 = 16 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (184 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (184 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_184 :
    recurrence4Scalar0Main.coeff 184 =
      (((((194557461127379 * 10 ^ 70 +
        2261987150886498250005831733687511074156056806403973440492222092921649) * 10 ^ 70 +
        0997198763205093286248524868118318094445747835115211559449083080793547) * 10 ^ 70 +
        0505232153476259035066063230106269509853991688474813424862999384497072) * 10 ^ 70 +
        5439151068440363795675396971009176433302550952020098172572238559265104) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (184 - x)) = _
  rw [show 185 = 1 +
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
    rw [show 24 = 16 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (185 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (185 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_185 :
    recurrence4Scalar0Main.coeff 185 =
      -(((((504662988186083 * 10 ^ 70 +
        2770640678022735384568640458746789261779029689155505748636804211506280) * 10 ^ 70 +
        5714199634283612581220429149634329877613206737093054755186726994513086) * 10 ^ 70 +
        1740046470835745047747479518019855615367587627218299188756923703215156) * 10 ^ 70 +
        9750173830752027301106728377377766018755556844958038868785914889510994) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (185 - x)) = _
  rw [show 186 = 1 +
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
    rw [show 25 = 16 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (186 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (186 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_186 :
    recurrence4Scalar0Main.coeff 186 =
      (((((1290130502019606 * 10 ^ 70 +
        5548211989287311573374616869090137056341588358076457038464274755117154) * 10 ^ 70 +
        4516948954393647845696035710328493409852729666029142904908261697695378) * 10 ^ 70 +
        6281691212914850147297598271673746000812816076614261042803148924025335) * 10 ^ 70 +
        2455054894824102519501787143387424485719530546007903713989320136747752) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (186 - x)) = _
  rw [show 187 = 1 +
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
    rw [show 26 = 16 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (187 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (187 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_187 :
    recurrence4Scalar0Main.coeff 187 =
      -(((((3250567052681496 * 10 ^ 70 +
        7469707432218090727650226044776506296248971897030730311486610504416127) * 10 ^ 70 +
        4244791871227280064435113103473229049946036308447340494083567244885946) * 10 ^ 70 +
        1068449634535842264555692437583968668030943450601496771778618406847782) * 10 ^ 70 +
        2671392405878116777415793646516039965177070777967057963488423031341726) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (187 - x)) = _
  rw [show 188 = 1 +
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
    rw [show 27 = 16 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (188 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (188 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_188 :
    recurrence4Scalar0Main.coeff 188 =
      (((((8072199214836795 * 10 ^ 70 +
        0986091349649898489869528490860586389538020925462054269279508299749174) * 10 ^ 70 +
        8083594704750491700212297664456030564194409518651609491188490646861730) * 10 ^ 70 +
        1537643144990273377609013348931778334636522295675071722654150217820446) * 10 ^ 70 +
        3047285893983366818300918826488085149579581133452422479185018540842433) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (188 - x)) = _
  rw [show 189 = 1 +
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
    rw [show 28 = 16 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (189 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (189 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_189 :
    recurrence4Scalar0Main.coeff 189 =
      -(((((19758096930368025 * 10 ^ 70 +
        3945720295217417625423882147632570901838948698309220398943404987605655) * 10 ^ 70 +
        5715681371374346281636096590566782073232288630278752935460230548616147) * 10 ^ 70 +
        4566581541582216775504145692464667413700822416146946067478437526937593) * 10 ^ 70 +
        4924975259133494741865287415120945421123970447792070342472315212942740) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (189 - x)) = _
  rw [show 190 = 1 +
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
    rw [show 29 = 16 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (190 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (190 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_190 :
    recurrence4Scalar0Main.coeff 190 =
      (((((47668487354914659 * 10 ^ 70 +
        4363169960415694993936086741112678337201362927147325996115483390942828) * 10 ^ 70 +
        4081766347399922086614258109462875922916258628355887496158575699689181) * 10 ^ 70 +
        5643526404257698151107557686173662974376347435776125523017971205454415) * 10 ^ 70 +
        1155679832814153278723306262170613642065261556773300309849113688713312) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (190 - x)) = _
  rw [show 191 = 1 +
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
    rw [show 30 = 16 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (191 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (191 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_191 :
    recurrence4Scalar0Main.coeff 191 =
      -(((((113360680265058367 * 10 ^ 70 +
        9544264237976278036137754208743440285770113053705765346651186099164835) * 10 ^ 70 +
        7877998054185577347879572284695203954443156689103517500621910648444861) * 10 ^ 70 +
        0533548797718882271118743604995257838766038331540196966234688817304653) * 10 ^ 70 +
        8043917493810767326611716044022965506085746775378587428553489103315321) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (191 - x)) = _
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
    rw [show 31 = 16 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (192 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (192 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_192 :
    recurrence4Scalar0Main.coeff 192 =
      (((((265735386165045919 * 10 ^ 70 +
        0664527239649192973808202371016095324998052522500011118667519270325618) * 10 ^ 70 +
        7662924673698554459326967738671950149384425032042242660646603890109352) * 10 ^ 70 +
        0375394585178600562225671836168537505837448726870195033238015450114777) * 10 ^ 70 +
        9955830374359251532157114700790097195776619945118996546641703707038810) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (192 - x)) = _
  rw [show 193 = 1 +
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
    rw [show 32 = 16 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (193 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (193 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_193 :
    recurrence4Scalar0Main.coeff 193 =
      -(((((614048294635949066 * 10 ^ 70 +
        9924134175896557999672291562429969492846105431028246314532147110789784) * 10 ^ 70 +
        5331611801799382177212686745844294948005528836801087468029996213300576) * 10 ^ 70 +
        2353655737146511894398713888594961812707827192914305189336587251352191) * 10 ^ 70 +
        0973586060603871401154605224202234556461427766714955836884081183320838) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (193 - x)) = _
  rw [show 194 = 1 +
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
    rw [show 33 = 16 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (194 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (194 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_194 :
    recurrence4Scalar0Main.coeff 194 =
      (((((1398722061197489925 * 10 ^ 70 +
        2079502289440657290425278506015077048442960588079503605683816193300538) * 10 ^ 70 +
        5597636125499565809543712064184438928139295547459094784456362822817507) * 10 ^ 70 +
        7259360959666181243235877451957922458650947105903700550831330532564356) * 10 ^ 70 +
        9789161187000181273838543479594871841182909402624801647914695658449385) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (194 - x)) = _
  rw [show 195 = 1 +
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
    rw [show 34 = 16 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (195 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (195 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_195 :
    recurrence4Scalar0Main.coeff 195 =
      -(((((3140833186970267696 * 10 ^ 70 +
        0924204124822514152391688741906551827248149613357648322742308769502104) * 10 ^ 70 +
        2421791122993076465823909531237915263205414047935418408140846250383559) * 10 ^ 70 +
        3675921631119613186610333834863524623476102332550136347454141883239576) * 10 ^ 70 +
        1173994581752720819373236509112901066516940563910746569565349709976379) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (195 - x)) = _
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
    rw [show 35 = 16 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (196 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (196 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_196 :
    recurrence4Scalar0Main.coeff 196 =
      (((((6952658187483609459 * 10 ^ 70 +
        5385521098876230335893129139864763410915817158048381259468343607117393) * 10 ^ 70 +
        7683266726717566451494742407959220930118116849574347320621092196284417) * 10 ^ 70 +
        8367458850917709271165481234277670141357589425743114763510921470603728) * 10 ^ 70 +
        0921934254201562279214546272337559411690676340333495540666561565947987) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (196 - x)) = _
  rw [show 197 = 1 +
    196 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
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
    rw [show 36 = 16 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (197 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (197 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_197 :
    recurrence4Scalar0Main.coeff 197 =
      -(((((15172482772574122175 * 10 ^ 70 +
        5824034310707514915446321371961250652450245963235539361461063945705220) * 10 ^ 70 +
        9569118475560528329104524353489341131775867073352667560100924468974129) * 10 ^ 70 +
        7609356713823998620677571272135949243711348984470854787913593461757620) * 10 ^ 70 +
        9010467015010753045453626608972958741217572902823865941558953657090300) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (197 - x)) = _
  rw [show 198 = 1 +
    197 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
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
    rw [show 37 = 16 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (198 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (198 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_198 :
    recurrence4Scalar0Main.coeff 198 =
      (((((32641384560133045278 * 10 ^ 70 +
        5108265418085917467333090153843851382093286117146631778727122573958594) * 10 ^ 70 +
        4178690507925678749232916287144812146607069069071197128065383174140073) * 10 ^ 70 +
        9874161752217659392248912643806093299524372643387677132705090085935428) * 10 ^ 70 +
        6355952459165409062353408184719275563027882486083750402865630398798155) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (198 - x)) = _
  rw [show 199 = 1 +
    198 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
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
    rw [show 38 = 16 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (199 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (199 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_199 :
    recurrence4Scalar0Main.coeff 199 =
      -(((((69229653831770826639 * 10 ^ 70 +
        8410699673037350561776704939174803990961512289911356028815192578468860) * 10 ^ 70 +
        7713621013272784976445208083779809974845698774461404970200416645689446) * 10 ^ 70 +
        7089002957852993464436970987881819172277618511396758316347930282413325) * 10 ^ 70 +
        2716260555432663398735444779351412023563103794218946501452077565038629) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (199 - x)) = _
  rw [show 200 = 1 +
    199 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
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
    rw [show 39 = 16 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (200 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (200 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_200 :
    recurrence4Scalar0Main.coeff 200 =
      (((((144754494370116973594 * 10 ^ 70 +
        0408342946467024384718197224975709243931749189702538206931016948148523) * 10 ^ 70 +
        2295072464005916006819726670329069989159250895654883977420786528590115) * 10 ^ 70 +
        4561824703629574261414358226068621018707746893795637344333633178872548) * 10 ^ 70 +
        5168351891583932426409733039944212557836944534616477892371209368911123) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (200 - x)) = _
  rw [show 201 = 1 +
    200 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
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
    rw [show 40 = 16 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (201 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (201 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_201 :
    recurrence4Scalar0Main.coeff 201 =
      -(((((298395302908907079623 * 10 ^ 70 +
        3638113880760056258198574324095274374251076825524582293516409493456037) * 10 ^ 70 +
        1478388241338762045594988113979323438937979137854920127944325482260935) * 10 ^ 70 +
        4787170176422500926726057151994777477075247795110640433393080795546991) * 10 ^ 70 +
        1159343291074587937327350674171867157250291785976365679405097761469172) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (201 - x)) = _
  rw [show 202 = 1 +
    201 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
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
    rw [show 41 = 16 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (202 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (202 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_202 :
    recurrence4Scalar0Main.coeff 202 =
      (((((606421651309463205197 * 10 ^ 70 +
        0271904228559899542024436536539714169801545769376840533155681270136180) * 10 ^ 70 +
        9862064238276916792964422938742673058740281111652388934596333411883280) * 10 ^ 70 +
        8980799624517470156447180665066316879154826348321214874281127086212565) * 10 ^ 70 +
        0357845419764121530109799861842351514397096506697401419471958796347073) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (202 - x)) = _
  rw [show 203 = 1 +
    202 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
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
    rw [show 42 = 16 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (203 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (203 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_203 :
    recurrence4Scalar0Main.coeff 203 =
      -(((((1215015898956361839175 * 10 ^ 70 +
        1609241393377883672299818827079202391400970530033708040775726172092765) * 10 ^ 70 +
        8036153568721135325872950187126922688261725241409782111066078196892937) * 10 ^ 70 +
        3118418359521546477240104784641225877936447236411048076942143391212154) * 10 ^ 70 +
        0942061507701906623570094377197184565240020274055679693051028903625980) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (203 - x)) = _
  rw [show 204 = 1 +
    203 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
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
    rw [show 43 = 16 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (204 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (204 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_204 :
    recurrence4Scalar0Main.coeff 204 =
      (((((2400017825429196184187 * 10 ^ 70 +
        2037704379394176839252095373457591852403953727625241685465295027171086) * 10 ^ 70 +
        9569371092294896335096820544911374362946372488986096339095799578836106) * 10 ^ 70 +
        8192762998669492368159176275309239965627248339010645629347938628459492) * 10 ^ 70 +
        3500190714758331887935746947555837561144000306350368427276098389296347) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (204 - x)) = _
  rw [show 205 = 1 +
    204 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
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
    rw [show 44 = 16 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (205 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (205 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_205 :
    recurrence4Scalar0Main.coeff 205 =
      -(((((4673818020907277530326 * 10 ^ 70 +
        9107195271655277137939538358848256417048711102941230415497609328648585) * 10 ^ 70 +
        4762280900158936459626636884552989652030809338820748689759847208540829) * 10 ^ 70 +
        3013434657228378338796140166838626841891570965819196757910849566443354) * 10 ^ 70 +
        1012316962184376459663790790377346363676005822134189470539462334620368) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (205 - x)) = _
  rw [show 206 = 1 +
    205 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
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
    rw [show 45 = 16 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (206 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (206 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_206 :
    recurrence4Scalar0Main.coeff 206 =
      (((((8973303362595724903074 * 10 ^ 70 +
        6568457776799203066164071672042506282530724237339480516456114421442436) * 10 ^ 70 +
        7183847252245907247074375716305594971894324328255162718825114917829595) * 10 ^ 70 +
        1839137141487249804108675952954316385565772099160136509699696832635629) * 10 ^ 70 +
        6748901343688026468897107268360547070428263734558322902168346979867288) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (206 - x)) = _
  rw [show 207 = 1 +
    206 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
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
    rw [show 46 = 16 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (207 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (207 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_207 :
    recurrence4Scalar0Main.coeff 207 =
      -(((((16984519044061606634427 * 10 ^ 70 +
        2652684282640515587063062805194311024289774521730183626192430937102181) * 10 ^ 70 +
        9683898363432807717738131506037587933227996703568924365097011983599689) * 10 ^ 70 +
        1197491788679028241153357605607276050929110722369516550138905125755599) * 10 ^ 70 +
        3194281271572419232015293017194132671144395599928796859190422565136624) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (207 - x)) = _
  rw [show 208 = 1 +
    207 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
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
    rw [show 47 = 16 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (208 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (208 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_208 :
    recurrence4Scalar0Main.coeff 208 =
      (((((31693506141692078909140 * 10 ^ 70 +
        1662464155182005260738293933368141359698516698919890495580085576255027) * 10 ^ 70 +
        0097535431457383778070486072832762357606568364573196631301393053381913) * 10 ^ 70 +
        5264799148777112227541033426503384498011108269256197186268787870935334) * 10 ^ 70 +
        4174944052989711357246763955478172442068238561876806831656710009007993) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (208 - x)) = _
  rw [show 209 = 1 +
    208 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
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
    rw [show 48 = 16 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (209 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (209 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_209 :
    recurrence4Scalar0Main.coeff 209 =
      -(((((58303922358194559079098 * 10 ^ 70 +
        9062931107391548726935198631732860025570569632418460552098779334147958) * 10 ^ 70 +
        8432121590113159937599740422656903681803706119848033164549327939111497) * 10 ^ 70 +
        9865277217838058247700229477470040668451247299950192967673484218815581) * 10 ^ 70 +
        0981229532796353362556702735709096901081029242361686384975645136222300) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (209 - x)) = _
  rw [show 210 = 1 +
    209 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
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
    rw [show 49 = 16 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (210 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (210 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_210 :
    recurrence4Scalar0Main.coeff 210 =
      (((((105737360029190930509605 * 10 ^ 70 +
        2835489183047952549385793776998932797091212588776232188920807758966619) * 10 ^ 70 +
        5192445081613740429126448979315030052059666214403328462405544171696904) * 10 ^ 70 +
        4069188136453666153026844542382084944595716368019292615463495332676254) * 10 ^ 70 +
        0533502644553891609861950680724155162772802443071487970935780119082512) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (210 - x)) = _
  rw [show 211 = 1 +
    210 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
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
    rw [show 50 = 16 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (211 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (211 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_211 :
    recurrence4Scalar0Main.coeff 211 =
      -(((((189039866162424230420278 * 10 ^ 70 +
        6706705763643587486098636890016387977296902610445445649071908817299661) * 10 ^ 70 +
        5276417102215455055273788680343768247430465822173832176973966397879514) * 10 ^ 70 +
        4652950419011747126526020980960780583729931460479813023418292675078298) * 10 ^ 70 +
        7176643661792489521251323374151046045801433685206862059061309764642321) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (211 - x)) = _
  rw [show 212 = 1 +
    211 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
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
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (212 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (212 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_212 :
    recurrence4Scalar0Main.coeff 212 =
      (((((333166838240289480146560 * 10 ^ 70 +
        0360098308057139610739292080661015643250555985431267874152026175701221) * 10 ^ 70 +
        0295920162059151117041199155530507759736461505638773047486982595002677) * 10 ^ 70 +
        3391691554201892288997677151806371046677511248616601783584584760296271) * 10 ^ 70 +
        3134551415460418466584622913132126368720343998995662541950293587358900) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (212 - x)) = _
  rw [show 213 = 1 +
    212 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
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
    rw [show 52 = 16 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (213 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (213 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_213 :
    recurrence4Scalar0Main.coeff 213 =
      -(((((578816228937237891797277 * 10 ^ 70 +
        1342463326378169389466341157624238708142337203531948404582936780329428) * 10 ^ 70 +
        3200032759518322895110767764133031103261683557360733637708045157065936) * 10 ^ 70 +
        5520084518741202406583697873245066062296520524179146266604127482395278) * 10 ^ 70 +
        6471845379800193096385259365138272459730250178704353703570839764175558) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (213 - x)) = _
  rw [show 214 = 1 +
    213 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
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
    rw [show 53 = 16 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (214 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (214 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_214 :
    recurrence4Scalar0Main.coeff 214 =
      (((((991231473750250530539750 * 10 ^ 70 +
        9651724168058040330817211741606798067671031339853035652293721091964914) * 10 ^ 70 +
        9668038892567672274410525310540926870178183876668177127694270881419374) * 10 ^ 70 +
        1857733853585279657065996452033229492618565706742612845090622205855271) * 10 ^ 70 +
        6210479687331445176496439463788438887299862862049673933015406829872340) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (214 - x)) = _
  rw [show 215 = 1 +
    214 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
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
    rw [show 54 = 16 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (215 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (215 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_215 :
    recurrence4Scalar0Main.coeff 215 =
      -(((((1673197899819372513763956 * 10 ^ 70 +
        8551779816540573356677784818040145616561743930509715060807787949056819) * 10 ^ 70 +
        3241328316646204016411308080864742332150565790929972170929870689546342) * 10 ^ 70 +
        3715121480707709026791766964368030148849032172565382088359611272855534) * 10 ^ 70 +
        5485597467800056775415869300238964916344810448875577471142458825585404) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (215 - x)) = _
  rw [show 216 = 1 +
    215 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
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
    rw [show 55 = 16 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (216 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (216 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_216 :
    recurrence4Scalar0Main.coeff 216 =
      (((((2783793360676664016520556 * 10 ^ 70 +
        3392388324786569296795287996211141660894566397215286954821327772730187) * 10 ^ 70 +
        2947063506593499229654878233259499325034706434536229723066613673100792) * 10 ^ 70 +
        3299047306483026828418153375447435154642992351118247763443207920881288) * 10 ^ 70 +
        7655663417360755919702356204345650347820993811667560183588738846090943) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (216 - x)) = _
  rw [show 217 = 1 +
    216 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
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
    rw [show 56 = 16 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (217 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (217 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_217 :
    recurrence4Scalar0Main.coeff 217 =
      -(((((4564788249980323395983317 * 10 ^ 70 +
        1907675842802679550186362284213324704395653109198245641901202460707140) * 10 ^ 70 +
        5280648931916052907503041792141242282691914062003864886024885479635720) * 10 ^ 70 +
        9326213098246752258808686921793082374418313620079786462099540366409514) * 10 ^ 70 +
        9657698044895426221584226969827324370794988024692750755126590385201308) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (217 - x)) = _
  rw [show 218 = 1 +
    217 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
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
    rw [show 57 = 16 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (218 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (218 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_218 :
    recurrence4Scalar0Main.coeff 218 =
      (((((7376854750426866812303807 * 10 ^ 70 +
        5842995250895460193452202032675530371742428839751250964922602485674419) * 10 ^ 70 +
        9715060573469708002736045447059906453511682115346351968514127581611838) * 10 ^ 70 +
        4731082983074595086364588876260064929732424875888223310357675241680854) * 10 ^ 70 +
        8690979363349725478254409012217957411304214971493499110211620966123265) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (218 - x)) = _
  rw [show 219 = 1 +
    218 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
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
    rw [show 58 = 16 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (219 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (219 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_219 :
    recurrence4Scalar0Main.coeff 219 =
      -(((((11747834191366161143898773 * 10 ^ 70 +
        8235015613275785311075589696290533092193130748320379202055008370107126) * 10 ^ 70 +
        3268196041521884873302808779465077176273776912098706047064409859165603) * 10 ^ 70 +
        2690399994433108070571329438626576691124684542882457727279178522066357) * 10 ^ 70 +
        0096142333025560899315370143558856777924224265641950974122774839061806) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (219 - x)) = _
  rw [show 220 = 1 +
    219 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
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
    rw [show 59 = 16 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (220 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (220 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_220 :
    recurrence4Scalar0Main.coeff 220 =
      (((((18435073118025289460075611 * 10 ^ 70 +
        8111216885999511224079854704552589148016933764967254658911677688966842) * 10 ^ 70 +
        1560087945425050808141847129503656803789833539589727610692615143129640) * 10 ^ 70 +
        2727229098103955587258873692219377951967546085130919261868985274669877) * 10 ^ 70 +
        1828631986020732249999996993549992600489554843914430940005778920644381) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (220 - x)) = _
  rw [show 221 = 1 +
    220 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
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
    rw [show 60 = 16 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (221 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (221 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_221 :
    recurrence4Scalar0Main.coeff 221 =
      -(((((28503074646046906757061206 * 10 ^ 70 +
        6840433841602541509757643916399246843706428846797136124085403271547899) * 10 ^ 70 +
        3474392393848938338044647333636320980095926429565968100405507180013238) * 10 ^ 70 +
        6099158045424373139163337953431451209097690461156980606987650455485817) * 10 ^ 70 +
        3171324217334963156176265376203210381370921719767189878829345191414503) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (221 - x)) = _
  rw [show 222 = 1 +
    221 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
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
    rw [show 61 = 16 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (222 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (222 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_222 :
    recurrence4Scalar0Main.coeff 222 =
      (((((43416185198649170438310992 * 10 ^ 70 +
        4276881049724379857090461631254559513795615930671376048807732116392230) * 10 ^ 70 +
        3050778835183691283183407531983306799512543453362949407242946798440411) * 10 ^ 70 +
        8991048314160426167099739029172527051672526149272238693561174618077912) * 10 ^ 70 +
        6654447649987281747086713999163178142989916634079116620942005144651094) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (222 - x)) = _
  rw [show 223 = 1 +
    222 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
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
    rw [show 62 = 16 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (223 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (223 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_223 :
    recurrence4Scalar0Main.coeff 223 =
      -(((((65143496393151812568600100 * 10 ^ 70 +
        0258507758419116826521659037552606505762644235716055470522481989935430) * 10 ^ 70 +
        2316861516762836642020439778261817014832150521642281618588691655831781) * 10 ^ 70 +
        4482741721790249712525148269439526875501929705204619308137749525060817) * 10 ^ 70 +
        3997209412363875297937129888559374808786812006716831734606464606310190) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (223 - x)) = _
  rw [show 224 = 1 +
    223 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
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
    rw [show 63 = 16 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (224 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (224 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_224 :
    recurrence4Scalar0Main.coeff 224 =
      (((((96269364454585570568480920 * 10 ^ 70 +
        1645314936088451297159425995415934253290728903244183149227930851224711) * 10 ^ 70 +
        3533987579580864567700475702635346198565406470668450944301147616233236) * 10 ^ 70 +
        6314735503239605277197976689587533318813772249810331046255740537780676) * 10 ^ 70 +
        9365558532838718149701543334490373733902529897215848305387919732549851) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (224 - x)) = _
  rw [show 225 = 1 +
    224 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
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
    rw [show 64 = 16 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (225 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (225 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_225 :
    recurrence4Scalar0Main.coeff 225 =
      -(((((140097805114806458355469202 * 10 ^ 70 +
        3385372836537997491965795596973707572746433627514738538060086860375135) * 10 ^ 70 +
        4886882402357810141899590656907064850482012041248839566915583757128426) * 10 ^ 70 +
        7715507916943339376740406880990713755228326923290478808066262898574640) * 10 ^ 70 +
        0650722485249590584678295674740330926161151869206713526978113433989531) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (225 - x)) = _
  rw [show 226 = 1 +
    225 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
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
    rw [show 65 = 16 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (226 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (226 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_226 :
    recurrence4Scalar0Main.coeff 226 =
      (((((200732559734524803685068694 * 10 ^ 70 +
        4149135063346897559486216107631969167821285562373099710132421296100050) * 10 ^ 70 +
        2021277908921346876707997364927774675942116377362248234336703783270638) * 10 ^ 70 +
        8307982952253656937974937969994344038866345541617911189063533867252632) * 10 ^ 70 +
        5108800412456472550302043527010940831689820328630312329061358730807089) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (226 - x)) = _
  rw [show 227 = 1 +
    226 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
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
    rw [show 66 = 16 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (227 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (227 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_227 :
    recurrence4Scalar0Main.coeff 227 =
      -(((((283107176512928375988451676 * 10 ^ 70 +
        5203228446242456175471581271088828114486483753873658284081070308751728) * 10 ^ 70 +
        4455562045281244915559597056435928348646287462440419859472544439968479) * 10 ^ 70 +
        6489759866342076013934465868945987801979371793088528316964117380584238) * 10 ^ 70 +
        8191552612380983982954995846117236971886660192504972435255412625609230) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (227 - x)) = _
  rw [show 228 = 1 +
    227 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
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
    rw [show 67 = 16 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (228 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (228 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_228 :
    recurrence4Scalar0Main.coeff 228 =
      (((((392931714660697324066882935 * 10 ^ 70 +
        0456436729656667462784910264755748813722321818138894640739399684692654) * 10 ^ 70 +
        3713676357276153017101970758242825285596261579849794996200088616741350) * 10 ^ 70 +
        3982048184950267714432860405976980034284019778472680499356916705530402) * 10 ^ 70 +
        7361378838570936030111285621350041475815611780107258143627979595155515) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (228 - x)) = _
  rw [show 229 = 1 +
    228 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
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
    rw [show 68 = 16 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (229 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (229 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_229 :
    recurrence4Scalar0Main.coeff 229 =
      -(((((536515815879589323963049577 * 10 ^ 70 +
        9091960781952156054330086653991352177764759065391087182053102909953505) * 10 ^ 70 +
        4613319811921442343064428175391082438741818729406302507559042354390350) * 10 ^ 70 +
        0115763312927694541057475723978084511667961909053668602619951182340555) * 10 ^ 70 +
        0147979983537679719700382660810417986779200773827454662594964425288297) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (229 - x)) = _
  rw [show 230 = 1 +
    229 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
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
    rw [show 69 = 16 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (230 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (230 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_230 :
    recurrence4Scalar0Main.coeff 230 =
      (((((720423521989912734934058858 * 10 ^ 70 +
        1795727384686597425824667012253365027971247400326452445908103258058213) * 10 ^ 70 +
        8370912622252690371259707256225675575628972405399835827305957101921377) * 10 ^ 70 +
        3763941193689705258347995983004048739039073061740199312737644429751859) * 10 ^ 70 +
        5329136244520933249097313693115471431944281267039754367108416308900346) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (230 - x)) = _
  rw [show 231 = 1 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
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
    rw [show 70 = 16 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (231 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (231 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_231 :
    recurrence4Scalar0Main.coeff 231 =
      -(((((950915372675416542635250040 * 10 ^ 70 +
        8356700885356546587526265428785367663418625984790582287647954696853821) * 10 ^ 70 +
        1306280453540272328247019726669887202055510308874763107233841164220975) * 10 ^ 70 +
        8486111555588365616933985483013530449648970199841789535790849709189682) * 10 ^ 70 +
        0561048960407905590907816673599480104999745164033909290740129739108036) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (231 - x)) = _
  rw [show 232 = 1 +
    231 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
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
    rw [show 71 = 16 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (232 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (232 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_232 :
    recurrence4Scalar0Main.coeff 232 =
      (((((1233140220133989119002057795 * 10 ^ 70 +
        4119306064860100819465212037465508470081493533700585432207149549155069) * 10 ^ 70 +
        7804449880305015748374012441533737411276159413019674574251815821565847) * 10 ^ 70 +
        8833749967114345857984946290210410673408965838057721149948650842433470) * 10 ^ 70 +
        2818098698743626407572222814154521546880241799134165155099002511375877) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (232 - x)) = _
  rw [show 233 = 1 +
    232 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
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
    rw [show 72 = 16 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (233 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (233 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_233 :
    recurrence4Scalar0Main.coeff 233 =
      -(((((1570054948954223646715648813 * 10 ^ 70 +
        0782337612150866440212900165063091830315747974004949845605668933190570) * 10 ^ 70 +
        8010977397768913509716422702094718236263276183343752054963232050485556) * 10 ^ 70 +
        7717345944170361038287553390818501723498531942617042130156985958128567) * 10 ^ 70 +
        7705632605524098504117547919115679673661411058420975184902026792842164) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (233 - x)) = _
  rw [show 234 = 1 +
    233 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
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
    rw [show 73 = 16 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (234 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (234 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_234 :
    recurrence4Scalar0Main.coeff 234 =
      (((((1961076403263019081393583265 * 10 ^ 70 +
        8994781590254016014325759175229608927971006044844003580983707867250256) * 10 ^ 70 +
        6355373335491911386758380557791461088035674783037897199746734238031097) * 10 ^ 70 +
        1948494556926186419187622861288615210550799276558902864186186531768210) * 10 ^ 70 +
        9186013926665700220636703625232621978032901019240804403696475292246142) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (234 - x)) = _
  rw [show 235 = 1 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
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
    rw [show 74 = 16 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (235 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (235 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_235 :
    recurrence4Scalar0Main.coeff 235 =
      -(((((2400506673596582658453674769 * 10 ^ 70 +
        0463805546874145345178875635749902685540275408625345247200847870864770) * 10 ^ 70 +
        4519770729750880801018445979700755181044863210821942944962019929048853) * 10 ^ 70 +
        7057606340084973720291541793125713412291237109322606593030614356986402) * 10 ^ 70 +
        5766073654247240964236928999795562966612879030572512437824151612208970) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (235 - x)) = _
  rw [show 236 = 1 +
    235 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
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
    rw [show 75 = 16 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (236 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (236 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_236 :
    recurrence4Scalar0Main.coeff 236 =
      (((((2875819157709807281428921661 * 10 ^ 70 +
        6758324308268623233326122468149455236324851468269640541917831327272883) * 10 ^ 70 +
        6881750232252837682019933198758590305655820258222306944013147443726088) * 10 ^ 70 +
        3533215556912008766316873170902587534398239227865042447788011207121064) * 10 ^ 70 +
        3234973777367811443677469075054282697159335915179575258889644466783218) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (236 - x)) = _
  rw [show 237 = 1 +
    236 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
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
    rw [show 76 = 16 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (237 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (237 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_237 :
    recurrence4Scalar0Main.coeff 237 =
      -(((((3365945004846543213295839773 * 10 ^ 70 +
        6601680529618940653439841698886093790807233804634632360360038790273917) * 10 ^ 70 +
        8637453689976884824061397538469688333237999141400381670760043543779412) * 10 ^ 70 +
        1187065319928791214125837093159366657295870063315822026162047418731723) * 10 ^ 70 +
        3706462124542919964587199133164158699684935056073277785777606556177491) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (237 - x)) = _
  rw [show 238 = 1 +
    237 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
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
    rw [show 77 = 16 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (238 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (238 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_238 :
    recurrence4Scalar0Main.coeff 238 =
      (((((3839751848235163888633406390 * 10 ^ 70 +
        3903720584868259652122261078225603654189560984935053027398858214053093) * 10 ^ 70 +
        6797943423632402191390123276150590132577804466377884372824839963312458) * 10 ^ 70 +
        2754827491574037272174447395595221492761961434412984540628855858628285) * 10 ^ 70 +
        0148105140764671354788580894711385745525794040769097483006577845212702) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (238 - x)) = _
  rw [show 239 = 1 +
    238 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
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
    rw [show 78 = 16 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (239 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (239 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_239 :
    recurrence4Scalar0Main.coeff 239 =
      -(((((4254951122408924917040065357 * 10 ^ 70 +
        5545974086999427416059568275753418535787451908184225729089620409306530) * 10 ^ 70 +
        1426347046920719778000123178590137200837911986381804205343159988240011) * 10 ^ 70 +
        8708024666440508359771172272560991153187334267701502726907396154147982) * 10 ^ 70 +
        0995658312842192386474062033056895510549686850164849789128687741797483) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (239 - x)) = _
  rw [show 240 = 1 +
    239 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
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
    rw [show 79 = 16 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (240 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (240 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_240 :
    recurrence4Scalar0Main.coeff 240 =
      (((((4557697257390557519003770556 * 10 ^ 70 +
        8334839157253535594553523145850813228619315584277364436861511654189901) * 10 ^ 70 +
        7138946980665257622006354121203354537028673990371371295605396221352597) * 10 ^ 70 +
        5368058469654962335604861309866819702151312484489289807149035356054293) * 10 ^ 70 +
        0154666154002929432461597455475621632374128588501153092048396648649094) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (240 - x)) = _
  rw [show 241 = 1 +
    240 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
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
    rw [show 80 = 16 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (241 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (241 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_241 :
    recurrence4Scalar0Main.coeff 241 =
      -(((((4683141863502441544112566955 * 10 ^ 70 +
        7595241660436043927848477416042183493955931844774950010484833542727492) * 10 ^ 70 +
        1481237875546321284789781289549374505979697286119597892460053477845281) * 10 ^ 70 +
        9376524820824053443746947036712106362067491565369977312013590087635356) * 10 ^ 70 +
        6193184747283318917016368032946415461731940496555645206232888228006816) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (241 - x)) = _
  rw [show 242 = 1 +
    241 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
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
    rw [show 81 = 16 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (242 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (242 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_242 :
    recurrence4Scalar0Main.coeff 242 =
      (((((4557170262285831750027954067 * 10 ^ 70 +
        6846793741230076706013834997676448943175666268820903912401397338930283) * 10 ^ 70 +
        3465407693768194725420162593723271901549055787881651289421218599341388) * 10 ^ 70 +
        0624875843242158468540830660034250225313364079659974225099824195161251) * 10 ^ 70 +
        6683468631017731984532911213766293051534337637698439403829108861814896) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (242 - x)) = _
  rw [show 243 = 1 +
    242 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
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
    rw [show 82 = 16 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (243 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (243 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_243 :
    recurrence4Scalar0Main.coeff 243 =
      -(((((4099471251934925218096505555 * 10 ^ 70 +
        0164250415368836368636891284397703248345915465115319468092143591117174) * 10 ^ 70 +
        8240213650091670174251937739342216261593872778208668923307341178757397) * 10 ^ 70 +
        8655468786063499002625302474166011599891854674420401158731151143821476) * 10 ^ 70 +
        8537521427307331808992366955036564624493472546305527696998917810405849) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (243 - x)) = _
  rw [show 244 = 1 +
    243 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
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
    rw [show 83 = 16 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (244 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (244 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_244 :
    recurrence4Scalar0Main.coeff 244 =
      (((((3227973810886439310184804158 * 10 ^ 70 +
        4995052074833937480539845072261423572436878600424841679482659640647475) * 10 ^ 70 +
        1206617096090354550972327026964569856813342131045346250939478179704490) * 10 ^ 70 +
        2773422226880694921298282318058615961843847049179017705330406111599640) * 10 ^ 70 +
        2741246805675546467197095941503924596880325125966930256634915833766179) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (244 - x)) = _
  rw [show 245 = 1 +
    244 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
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
    rw [show 84 = 16 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (245 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (245 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_245 :
    recurrence4Scalar0Main.coeff 245 =
      -(((((1864533037804197387886230220 * 10 ^ 70 +
        7462909865852540049489143663124097697359439101971153035641317157100760) * 10 ^ 70 +
        3407433816681927484576095954287477383335948083580456934282184358418485) * 10 ^ 70 +
        7666874010236134563152013047676009189222208163682151575473500615492086) * 10 ^ 70 +
        4783285341016479091069579819570619139032559715594013519705080243950311) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (245 - x)) = _
  rw [show 246 = 1 +
    245 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
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
    rw [show 85 = 16 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (246 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (246 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_246 :
    recurrence4Scalar0Main.coeff 246 =
      -(((((58424468134759004578128461 * 10 ^ 70 +
        7029731726901060440945060712392355614815709467808463891377767427888542) * 10 ^ 70 +
        7195683948234038446584492424126300165819887586345253242080706968159990) * 10 ^ 70 +
        1014143812847405590950170520816812488147362860725507963343336003267465) * 10 ^ 70 +
        2978796614508444886232965141013706409381213272323921907311563318112425) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (246 - x)) = _
  rw [show 247 = 1 +
    246 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
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
    rw [show 86 = 16 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (247 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (247 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_247 :
    recurrence4Scalar0Main.coeff 247 =
      (((((2590758448223446627294169559 * 10 ^ 70 +
        3671632993508097040981778023476937503767093843983174691766009425105972) * 10 ^ 70 +
        2900230225838578916104897548841503881523650999900655356662391840341137) * 10 ^ 70 +
        2833619884611493428274664310694054697812454492095099642114344007702615) * 10 ^ 70 +
        1343191221508743014085611952027266093508638443337935695938650571030969) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (247 - x)) = _
  rw [show 248 = 1 +
    247 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
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
    rw [show 87 = 16 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (248 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (248 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_248 :
    recurrence4Scalar0Main.coeff 248 =
      -(((((5757588013082425598326873354 * 10 ^ 70 +
        0215942138776316726848535388954179983609827544255485907991543500134176) * 10 ^ 70 +
        5490926149302739051601165753547242209554240737948613319063380350230841) * 10 ^ 70 +
        3131388205910870994014603919720026694315862078979767730212093290921133) * 10 ^ 70 +
        7661713667490955445623146490796244254408241064484528638590810984488304) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (248 - x)) = _
  rw [show 249 = 1 +
    248 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
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
    rw [show 88 = 16 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (249 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (249 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_249 :
    recurrence4Scalar0Main.coeff 249 =
      (((((9553092021058903259202409412 * 10 ^ 70 +
        6632247870150128687919839742711508416312949054776591982782272742398922) * 10 ^ 70 +
        3749104258584417605747792365749130488713020581818311916896383241832043) * 10 ^ 70 +
        1178449448511742207087377229186698557504774455387005457064722738044253) * 10 ^ 70 +
        8080036872222014346031518627720227089584029513148225423904461841496493) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (249 - x)) = _
  rw [show 250 = 1 +
    249 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
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
    rw [show 89 = 16 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (250 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (250 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_250 :
    recurrence4Scalar0Main.coeff 250 =
      -(((((13935877327629295308042696280 * 10 ^ 70 +
        1076926453556179557697547479773277544199213404231177399052240311152539) * 10 ^ 70 +
        2302905656897223371521318989622619958188242004239595523865160277273898) * 10 ^ 70 +
        7820911279010378460069188937036741574052124019110049299295436337847808) * 10 ^ 70 +
        1797780355401107978624061339432919411303849478921014719185758210551761) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (250 - x)) = _
  rw [show 251 = 1 +
    250 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
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
    rw [show 90 = 16 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (251 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (251 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_251 :
    recurrence4Scalar0Main.coeff 251 =
      (((((18826596313348861416682812645 * 10 ^ 70 +
        2129471880273059111022875856277614563108395758913838873233476648466009) * 10 ^ 70 +
        1545146361650557998671094509654817982802606821248732088687438070330504) * 10 ^ 70 +
        5610197845876171911165355174576429037396306271540096526300654996182393) * 10 ^ 70 +
        6312441512879774627854303884321036622043558138043700090059118187509479) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (251 - x)) = _
  rw [show 252 = 1 +
    251 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 251 = 32 +
      219 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 219 = 32 +
      187 by norm_num, Finset.sum_range_add]
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
    rw [show 91 = 16 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (252 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (252 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_252 :
    recurrence4Scalar0Main.coeff 252 =
      -(((((24108343659493994412168926755 * 10 ^ 70 +
        9587257840893942863398723773654025027272319190202925151043833236529858) * 10 ^ 70 +
        4626949663765964354864885701328462933329580200994685759340242122604724) * 10 ^ 70 +
        9746141414804769461648592690910347904125103484474045138586503110457449) * 10 ^ 70 +
        6218430538946109747417403632611983626572178115218277757439889670784090) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (252 - x)) = _
  rw [show 253 = 1 +
    252 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 252 = 32 +
      220 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 220 = 32 +
      188 by norm_num, Finset.sum_range_add]
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
    rw [show 92 = 16 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (253 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (253 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_253 :
    recurrence4Scalar0Main.coeff 253 =
      (((((29630126859649570758330535110 * 10 ^ 70 +
        6536556408804215511234318069287185948209003309033218301690401062756724) * 10 ^ 70 +
        8402336756605035464014539877060519488520730558867364243579527102176731) * 10 ^ 70 +
        5955922094678096652029675845211656562009124584453877943679204760462488) * 10 ^ 70 +
        2722551107795271067503749097449421384979849687484172255241069441071789) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (253 - x)) = _
  rw [show 254 = 1 +
    253 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 253 = 32 +
      221 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 221 = 32 +
      189 by norm_num, Finset.sum_range_add]
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
    rw [show 93 = 16 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (254 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (254 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_254 :
    recurrence4Scalar0Main.coeff 254 =
      -(((((35213407200981625385372077648 * 10 ^ 70 +
        9278973831019294156917268811676073472983619647693485812665449152332516) * 10 ^ 70 +
        9257878201331799558889395737677231762577630645000269185832623209593490) * 10 ^ 70 +
        2427913194274973631354685575352258032295250541822085862202800192193666) * 10 ^ 70 +
        4746560767325722578807557927621796430259506646566126285483048460161872) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (254 - x)) = _
  rw [show 255 = 1 +
    254 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 254 = 32 +
      222 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 222 = 32 +
      190 by norm_num, Finset.sum_range_add]
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
    rw [show 94 = 16 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (255 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (255 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_255 :
    recurrence4Scalar0Main.coeff 255 =
      (((((40661381222122019828715392908 * 10 ^ 70 +
        4296427152431722283176372531909760324165254913862359226685837005571147) * 10 ^ 70 +
        1714465028423273734404711490552511159831474660590789979872296789491406) * 10 ^ 70 +
        0640218761421924272985666835464098384291871748747916839960740304065544) * 10 ^ 70 +
        0684422286047322614936969870275872637287249967822562711777760396847505) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (255 - x)) = _
  rw [show 256 = 1 +
    255 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 255 = 32 +
      223 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 223 = 32 +
      191 by norm_num, Finset.sum_range_add]
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
    rw [show 95 = 16 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (256 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (256 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_256 :
    recurrence4Scalar0Main.coeff 256 =
      -(((((45770357633236379337933707547 * 10 ^ 70 +
        9794160580238481583191520643605355588321799433869737303377185016250719) * 10 ^ 70 +
        4288718633732012853424828535025540482375712107038042781904534293502033) * 10 ^ 70 +
        5751668196842825292113020574666886081708541058360411083945503862303907) * 10 ^ 70 +
        0313244442106173107792195343189222547677633523823847711626115222041758) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (256 - x)) = _
  rw [show 257 = 1 +
    256 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 256 = 32 +
      224 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 224 = 32 +
      192 by norm_num, Finset.sum_range_add]
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
    rw [show 96 = 16 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (257 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (257 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_257 :
    recurrence4Scalar0Main.coeff 257 =
      (((((50342323619984184079818495942 * 10 ^ 70 +
        9276178315089020108982351896708591241968794222450982341503651985462113) * 10 ^ 70 +
        2253115231314030243701672385617974171873797451392836090602139014714828) * 10 ^ 70 +
        1940419423104246721612577581901029832139894058774380877209910587844858) * 10 ^ 70 +
        9068303021381251562462479191470092114115090426748863660444971372808187) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (257 - x)) = _
  rw [show 258 = 1 +
    257 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 257 = 32 +
      225 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
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
    rw [show 97 = 16 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (258 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (258 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_258 :
    recurrence4Scalar0Main.coeff 258 =
      -(((((54197624653967149695176024136 * 10 ^ 70 +
        0628338533144728654313539400003267759450806488807917731201395005142543) * 10 ^ 70 +
        6566293714104898932993896671460583033265203437891751100887389828189670) * 10 ^ 70 +
        7006163633043092376792231598612783479999272797217903805391130960312110) * 10 ^ 70 +
        9858327306202565612758708252557847301091067027079040929946372591935753) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (258 - x)) = _
  rw [show 259 = 1 +
    258 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 258 = 32 +
      226 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
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
    rw [show 98 = 16 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (259 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (259 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_259 :
    recurrence4Scalar0Main.coeff 259 =
      (((((57186629663546873045412276329 * 10 ^ 70 +
        7574902538364362238181514777075270755710769646214196941193704675406596) * 10 ^ 70 +
        9371255378245570590903554475420736021253754851660575367341253258612844) * 10 ^ 70 +
        8214119537767565170084020815306040749180037593331317429095294401515436) * 10 ^ 70 +
        6948712076072871688065841674637276221455649244285948448645402953680766) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (259 - x)) = _
  rw [show 260 = 1 +
    259 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 259 = 32 +
      227 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
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
    rw [show 99 = 16 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (260 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (260 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_260 :
    recurrence4Scalar0Main.coeff 260 =
      -(((((59199329356625437071521038169 * 10 ^ 70 +
        6448315903387522422627789682969194102309577208428997492398766391546952) * 10 ^ 70 +
        1796101801467565921035745393949858499822797180231679467154986875501383) * 10 ^ 70 +
        8076346353660884223420371050913500085122469869810382874648156762257747) * 10 ^ 70 +
        3874313427037066834199912256692122205505369897543719875172327684113528) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (260 - x)) = _
  rw [show 261 = 1 +
    260 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 260 = 32 +
      228 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 16 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (261 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (261 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_261 :
    recurrence4Scalar0Main.coeff 261 =
      (((((60172012599744995288894168836 * 10 ^ 70 +
        9658892254697540192277037982262947879275698402682062790284848483038271) * 10 ^ 70 +
        4082153067697159742608755500629263736675050428091190601634890690949354) * 10 ^ 70 +
        2345108665860611353026342873649305115250400952422365527087504331645414) * 10 ^ 70 +
        6830302128500456142513253664371672265270682772812062412128449048229868) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (261 - x)) = _
  rw [show 262 = 1 +
    261 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 261 = 32 +
      229 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 16 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (262 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (262 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_262 :
    recurrence4Scalar0Main.coeff 262 =
      -(((((60090460065637001789468993062 * 10 ^ 70 +
        4339260292531952821171185119764076431507578402817178490349236062654615) * 10 ^ 70 +
        5687916297275837195855763929263077261602579609226415583863734783721100) * 10 ^ 70 +
        6721433314674682528790674986920806750995573490038146510050845058108462) * 10 ^ 70 +
        3514136059649021172857652272654798785014690677937545091418296826148335) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (262 - x)) = _
  rw [show 263 = 1 +
    262 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 262 = 32 +
      230 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 16 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (263 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (263 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_263 :
    recurrence4Scalar0Main.coeff 263 =
      (((((58989448480038012601651661754 * 10 ^ 70 +
        4371977777864714335882710447220905138074215417604996026711207947356200) * 10 ^ 70 +
        0270236823260673602847547280133865909575322959470316898799164715741599) * 10 ^ 70 +
        6071492464462913691762323898192591399666270834705230560087998891938909) * 10 ^ 70 +
        5711679498297590886360172865252037199465798254179674962125923101982014) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (263 - x)) = _
  rw [show 264 = 1 +
    263 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 263 = 32 +
      231 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 16 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (264 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (264 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_264 :
    recurrence4Scalar0Main.coeff 264 =
      -(((((56948727654054044018051258601 * 10 ^ 70 +
        9152883188669745141142892453875657544348881426064403396909270530636303) * 10 ^ 70 +
        6493137831523389959730448240403502845631252369876797191429507236382309) * 10 ^ 70 +
        3306442849601615613736221469406813900876772611048379894873616330577064) * 10 ^ 70 +
        1073398719138388613224540583940901331779247898631482826503077531780891) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (264 - x)) = _
  rw [show 265 = 1 +
    264 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 264 = 32 +
      232 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 16 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (265 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (265 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_265 :
    recurrence4Scalar0Main.coeff 265 =
      (((((54085970181016802650277640969 * 10 ^ 70 +
        0139215668567262897239749059566149525070770973955423719884111353276890) * 10 ^ 70 +
        1999116436875173472359931608644373727913739120302556981892945377337533) * 10 ^ 70 +
        4692810414648833717043244213839411473156947746604897826094930715658411) * 10 ^ 70 +
        2402269971134481570601727236330326534277666273347051343114333945787771) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (265 - x)) = _
  rw [show 266 = 1 +
    265 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 265 = 32 +
      233 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 16 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (266 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (266 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_266 :
    recurrence4Scalar0Main.coeff 266 =
      -(((((50547460282718034354826401799 * 10 ^ 70 +
        1567917857873331882126227424690679013945605077895572259920271856007268) * 10 ^ 70 +
        1731494283266192972794708194842987276013358334143610205328005181784994) * 10 ^ 70 +
        9596727122775831141053334891322103374095458957016185119383876465161797) * 10 ^ 70 +
        5927536797475543400333164774157686345285367810548213599835532172652730) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (266 - x)) = _
  rw [show 267 = 1 +
    266 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 266 = 32 +
      234 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 16 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (267 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (267 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_267 :
    recurrence4Scalar0Main.coeff 267 =
      (((((46497455433466394699065495516 * 10 ^ 70 +
        0736213626634304233637319850522787256772702057889205523243429084557982) * 10 ^ 70 +
        4261058492171187427895259067838241478142182063027347292314676696235387) * 10 ^ 70 +
        2646782843385823324639624542084482592607121305249287796159653390109212) * 10 ^ 70 +
        9573135941384564529174280297799892585525060231275648549905255825225084) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (267 - x)) = _
  rw [show 268 = 1 +
    267 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 267 = 32 +
      235 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 16 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (268 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (268 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_268 :
    recurrence4Scalar0Main.coeff 268 =
      -(((((42107208697984143826218063302 * 10 ^ 70 +
        9267090999351082579662257925219807434996462540271970401044648381864124) * 10 ^ 70 +
        5603903017096106811351549125960585769804538414193952815632036786465126) * 10 ^ 70 +
        7332612720938464163960779520221202413966063860309896289561934990872890) * 10 ^ 70 +
        8491489902531065693887914148861495863389563875240257665224579726748020) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (268 - x)) = _
  rw [show 269 = 1 +
    268 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 268 = 32 +
      236 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 16 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (269 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (269 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_269 :
    recurrence4Scalar0Main.coeff 269 =
      (((((37544583697832009764192426927 * 10 ^ 70 +
        2034054778009759610735753547167055197856026462760767208041870080197717) * 10 ^ 70 +
        5705408901845992101315341966910506534506857923869346335260709245712521) * 10 ^ 70 +
        4592193926257857343559892310238537394422831041796621223478568383575737) * 10 ^ 70 +
        7974671429020731698543000294584602680051632441896520218311688318588502) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (269 - x)) = _
  rw [show 270 = 1 +
    269 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 269 = 32 +
      237 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 16 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (270 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (270 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_270 :
    recurrence4Scalar0Main.coeff 270 =
      -(((((32965044500253462428144066920 * 10 ^ 70 +
        1034141212458845591767514793237085252311988524396256656499969901592435) * 10 ^ 70 +
        5732257014056003741807000267454161308098940511496778183819534741362074) * 10 ^ 70 +
        7549287188951760275213582777357626161114943150158891039551834273763789) * 10 ^ 70 +
        4860904511468058201174787688219538437801995878328471373438450741611624) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (270 - x)) = _
  rw [show 271 = 1 +
    270 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 270 = 32 +
      238 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 16 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (271 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (271 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_271 :
    recurrence4Scalar0Main.coeff 271 =
      (((((28504586748499487901200439627 * 10 ^ 70 +
        3207547029888574433850643816071574012371319555393232346118352918519133) * 10 ^ 70 +
        3413251657129158191501650308164536159753780024152902987466090182010031) * 10 ^ 70 +
        8575419903383598625693489921293199019548472985397686438988214685905456) * 10 ^ 70 +
        4536744051054675799850879107009334130219968685774868366039083604949756) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (271 - x)) = _
  rw [show 272 = 1 +
    271 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 271 = 32 +
      239 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 16 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (272 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (272 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_272 :
    recurrence4Scalar0Main.coeff 272 =
      -(((((24274926839061116034028166860 * 10 ^ 70 +
        3105820100625149843460220149063939435973469881057006138464128821347111) * 10 ^ 70 +
        1755433233012316531135183904143194174193094136174433399429268478655118) * 10 ^ 70 +
        3847045846204039440208171592342223358625407656639788975565077151717687) * 10 ^ 70 +
        2334804953235016287443173142129708458806770720786687027101527714694719) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (272 - x)) = _
  rw [show 273 = 1 +
    272 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 272 = 32 +
      240 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 16 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (273 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (273 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_273 :
    recurrence4Scalar0Main.coeff 273 =
      (((((20361016041857458601942848966 * 10 ^ 70 +
        7097702853675928787151056670205062557932595372536056822485979401437591) * 10 ^ 70 +
        1747792469864240400647932127332350299222151243434626669675155917381760) * 10 ^ 70 +
        2141933180334462279487950379735474491911255079159451369911706123819686) * 10 ^ 70 +
        1258116763154733375119654103927598351138051823910697206603263403485735) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (273 - x)) = _
  rw [show 274 = 1 +
    273 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 273 = 32 +
      241 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 16 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (274 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (274 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_274 :
    recurrence4Scalar0Main.coeff 274 =
      -(((((16820724976265675904144996466 * 10 ^ 70 +
        2814490750124060756222576418749842872833405310099872459682768562670418) * 10 ^ 70 +
        7790990010024394163884946156025891701223036035878632490555678283439466) * 10 ^ 70 +
        0655431279918865787558882211281994126232005925347353412788433318400229) * 10 ^ 70 +
        7042774925347318590450094112997499685729763356979551080754755829038001) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (274 - x)) = _
  rw [show 275 = 1 +
    274 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 274 = 32 +
      242 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 16 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (275 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (275 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_275 :
    recurrence4Scalar0Main.coeff 275 =
      (((((13686371919179525915662105531 * 10 ^ 70 +
        1664472335857390440840526222968918235055895147177147725036552170256803) * 10 ^ 70 +
        5323909458339831144862988084988816781716658089325422917255851089276030) * 10 ^ 70 +
        6252706245876259741785841537828778148051555896254644574145791816277041) * 10 ^ 70 +
        0567851306226583950420397462603374824249303875705932767564508001044101) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (275 - x)) = _
  rw [show 276 = 1 +
    275 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 275 = 32 +
      243 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 16 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar0Main_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (276 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (276 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_276 :
    recurrence4Scalar0Main.coeff 276 =
      -(((((10967657702568847840785187737 * 10 ^ 70 +
        6603755487632461223133769931309368712580792283519907118380714595288029) * 10 ^ 70 +
        1631055372369462592922682135485926194396477663036505481615397835748951) * 10 ^ 70 +
        1857230980690619707029703202113579550244464060424455678630880523047046) * 10 ^ 70 +
        3446866442021715456571429596767762301218362662262296377932377382871557) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (276 - x)) = _
  rw [show 277 = 1 +
    276 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 276 = 32 +
      244 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 16 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
