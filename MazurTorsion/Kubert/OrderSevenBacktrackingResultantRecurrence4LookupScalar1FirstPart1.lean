/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB3A4
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar1First coefficient convolution

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
  recurrence4B3A4_coeff_0
  recurrence4B3A4_coeff_1
  recurrence4B3A4_coeff_10
  recurrence4B3A4_coeff_100
  recurrence4B3A4_coeff_101
  recurrence4B3A4_coeff_102
  recurrence4B3A4_coeff_103
  recurrence4B3A4_coeff_104
  recurrence4B3A4_coeff_105
  recurrence4B3A4_coeff_106
  recurrence4B3A4_coeff_107
  recurrence4B3A4_coeff_108
  recurrence4B3A4_coeff_109
  recurrence4B3A4_coeff_11
  recurrence4B3A4_coeff_110
  recurrence4B3A4_coeff_111

attribute [local simp]
  recurrence4B3A4_coeff_112
  recurrence4B3A4_coeff_113
  recurrence4B3A4_coeff_114
  recurrence4B3A4_coeff_115
  recurrence4B3A4_coeff_116
  recurrence4B3A4_coeff_117
  recurrence4B3A4_coeff_118
  recurrence4B3A4_coeff_119
  recurrence4B3A4_coeff_12
  recurrence4B3A4_coeff_120
  recurrence4B3A4_coeff_121
  recurrence4B3A4_coeff_122
  recurrence4B3A4_coeff_123
  recurrence4B3A4_coeff_124
  recurrence4B3A4_coeff_125
  recurrence4B3A4_coeff_126
  recurrence4B3A4_coeff_127
  recurrence4B3A4_coeff_128
  recurrence4B3A4_coeff_129
  recurrence4B3A4_coeff_13
  recurrence4B3A4_coeff_130
  recurrence4B3A4_coeff_131
  recurrence4B3A4_coeff_132
  recurrence4B3A4_coeff_133
  recurrence4B3A4_coeff_134
  recurrence4B3A4_coeff_135
  recurrence4B3A4_coeff_136
  recurrence4B3A4_coeff_137
  recurrence4B3A4_coeff_138
  recurrence4B3A4_coeff_139
  recurrence4B3A4_coeff_14
  recurrence4B3A4_coeff_140
  recurrence4B3A4_coeff_141
  recurrence4B3A4_coeff_142
  recurrence4B3A4_coeff_143
  recurrence4B3A4_coeff_144
  recurrence4B3A4_coeff_145
  recurrence4B3A4_coeff_146
  recurrence4B3A4_coeff_147
  recurrence4B3A4_coeff_148
  recurrence4B3A4_coeff_149
  recurrence4B3A4_coeff_15
  recurrence4B3A4_coeff_150
  recurrence4B3A4_coeff_151
  recurrence4B3A4_coeff_152
  recurrence4B3A4_coeff_153
  recurrence4B3A4_coeff_154
  recurrence4B3A4_coeff_155
  recurrence4B3A4_coeff_156
  recurrence4B3A4_coeff_157
  recurrence4B3A4_coeff_158
  recurrence4B3A4_coeff_159
  recurrence4B3A4_coeff_16
  recurrence4B3A4_coeff_160
  recurrence4B3A4_coeff_161
  recurrence4B3A4_coeff_162
  recurrence4B3A4_coeff_163
  recurrence4B3A4_coeff_164
  recurrence4B3A4_coeff_165
  recurrence4B3A4_coeff_166
  recurrence4B3A4_coeff_167
  recurrence4B3A4_coeff_168
  recurrence4B3A4_coeff_169
  recurrence4B3A4_coeff_17

attribute [local simp]
  recurrence4B3A4_coeff_170
  recurrence4B3A4_coeff_171
  recurrence4B3A4_coeff_172
  recurrence4B3A4_coeff_173
  recurrence4B3A4_coeff_174
  recurrence4B3A4_coeff_175
  recurrence4B3A4_coeff_176
  recurrence4B3A4_coeff_177
  recurrence4B3A4_coeff_178
  recurrence4B3A4_coeff_179
  recurrence4B3A4_coeff_18
  recurrence4B3A4_coeff_180
  recurrence4B3A4_coeff_181
  recurrence4B3A4_coeff_182
  recurrence4B3A4_coeff_183
  recurrence4B3A4_coeff_184
  recurrence4B3A4_coeff_185
  recurrence4B3A4_coeff_186
  recurrence4B3A4_coeff_187
  recurrence4B3A4_coeff_188
  recurrence4B3A4_coeff_189
  recurrence4B3A4_coeff_19
  recurrence4B3A4_coeff_190
  recurrence4B3A4_coeff_191
  recurrence4B3A4_coeff_192
  recurrence4B3A4_coeff_193
  recurrence4B3A4_coeff_194
  recurrence4B3A4_coeff_195
  recurrence4B3A4_coeff_196
  recurrence4B3A4_coeff_197
  recurrence4B3A4_coeff_198
  recurrence4B3A4_coeff_199
  recurrence4B3A4_coeff_2
  recurrence4B3A4_coeff_20
  recurrence4B3A4_coeff_200
  recurrence4B3A4_coeff_201
  recurrence4B3A4_coeff_202
  recurrence4B3A4_coeff_203
  recurrence4B3A4_coeff_204
  recurrence4B3A4_coeff_205
  recurrence4B3A4_coeff_206
  recurrence4B3A4_coeff_207
  recurrence4B3A4_coeff_208
  recurrence4B3A4_coeff_209
  recurrence4B3A4_coeff_21
  recurrence4B3A4_coeff_210
  recurrence4B3A4_coeff_211
  recurrence4B3A4_coeff_212
  recurrence4B3A4_coeff_213
  recurrence4B3A4_coeff_214
  recurrence4B3A4_coeff_215
  recurrence4B3A4_coeff_216
  recurrence4B3A4_coeff_217
  recurrence4B3A4_coeff_218
  recurrence4B3A4_coeff_219
  recurrence4B3A4_coeff_22
  recurrence4B3A4_coeff_220
  recurrence4B3A4_coeff_221
  recurrence4B3A4_coeff_222
  recurrence4B3A4_coeff_223
  recurrence4B3A4_coeff_224
  recurrence4B3A4_coeff_225
  recurrence4B3A4_coeff_226
  recurrence4B3A4_coeff_227

attribute [local simp]
  recurrence4B3A4_coeff_228
  recurrence4B3A4_coeff_229
  recurrence4B3A4_coeff_23
  recurrence4B3A4_coeff_230
  recurrence4B3A4_coeff_231
  recurrence4B3A4_coeff_232
  recurrence4B3A4_coeff_233
  recurrence4B3A4_coeff_234
  recurrence4B3A4_coeff_235
  recurrence4B3A4_coeff_236
  recurrence4B3A4_coeff_237
  recurrence4B3A4_coeff_238
  recurrence4B3A4_coeff_239
  recurrence4B3A4_coeff_24
  recurrence4B3A4_coeff_240
  recurrence4B3A4_coeff_241
  recurrence4B3A4_coeff_242
  recurrence4B3A4_coeff_243
  recurrence4B3A4_coeff_244
  recurrence4B3A4_coeff_245
  recurrence4B3A4_coeff_246
  recurrence4B3A4_coeff_247
  recurrence4B3A4_coeff_248
  recurrence4B3A4_coeff_249
  recurrence4B3A4_coeff_25
  recurrence4B3A4_coeff_250
  recurrence4B3A4_coeff_251
  recurrence4B3A4_coeff_252
  recurrence4B3A4_coeff_253
  recurrence4B3A4_coeff_254
  recurrence4B3A4_coeff_255
  recurrence4B3A4_coeff_256
  recurrence4B3A4_coeff_257
  recurrence4B3A4_coeff_258
  recurrence4B3A4_coeff_259
  recurrence4B3A4_coeff_26
  recurrence4B3A4_coeff_260
  recurrence4B3A4_coeff_261
  recurrence4B3A4_coeff_262
  recurrence4B3A4_coeff_263
  recurrence4B3A4_coeff_264
  recurrence4B3A4_coeff_265
  recurrence4B3A4_coeff_266
  recurrence4B3A4_coeff_267
  recurrence4B3A4_coeff_268
  recurrence4B3A4_coeff_269
  recurrence4B3A4_coeff_27
  recurrence4B3A4_coeff_270
  recurrence4B3A4_coeff_271
  recurrence4B3A4_coeff_272
  recurrence4B3A4_coeff_273
  recurrence4B3A4_coeff_274
  recurrence4B3A4_coeff_275
  recurrence4B3A4_coeff_28
  recurrence4B3A4_coeff_29
  recurrence4B3A4_coeff_3
  recurrence4B3A4_coeff_30
  recurrence4B3A4_coeff_31
  recurrence4B3A4_coeff_32
  recurrence4B3A4_coeff_33
  recurrence4B3A4_coeff_34
  recurrence4B3A4_coeff_35
  recurrence4B3A4_coeff_36
  recurrence4B3A4_coeff_37

attribute [local simp]
  recurrence4B3A4_coeff_38
  recurrence4B3A4_coeff_39
  recurrence4B3A4_coeff_4
  recurrence4B3A4_coeff_40
  recurrence4B3A4_coeff_41
  recurrence4B3A4_coeff_42
  recurrence4B3A4_coeff_43
  recurrence4B3A4_coeff_44
  recurrence4B3A4_coeff_45
  recurrence4B3A4_coeff_46
  recurrence4B3A4_coeff_47
  recurrence4B3A4_coeff_48
  recurrence4B3A4_coeff_49
  recurrence4B3A4_coeff_5
  recurrence4B3A4_coeff_50
  recurrence4B3A4_coeff_51
  recurrence4B3A4_coeff_52
  recurrence4B3A4_coeff_53
  recurrence4B3A4_coeff_54
  recurrence4B3A4_coeff_55
  recurrence4B3A4_coeff_56
  recurrence4B3A4_coeff_57
  recurrence4B3A4_coeff_58
  recurrence4B3A4_coeff_59
  recurrence4B3A4_coeff_6
  recurrence4B3A4_coeff_60
  recurrence4B3A4_coeff_61
  recurrence4B3A4_coeff_62
  recurrence4B3A4_coeff_63
  recurrence4B3A4_coeff_64
  recurrence4B3A4_coeff_65
  recurrence4B3A4_coeff_66
  recurrence4B3A4_coeff_67
  recurrence4B3A4_coeff_68
  recurrence4B3A4_coeff_69
  recurrence4B3A4_coeff_7
  recurrence4B3A4_coeff_70
  recurrence4B3A4_coeff_71
  recurrence4B3A4_coeff_72
  recurrence4B3A4_coeff_73
  recurrence4B3A4_coeff_74
  recurrence4B3A4_coeff_75
  recurrence4B3A4_coeff_76
  recurrence4B3A4_coeff_77
  recurrence4B3A4_coeff_78
  recurrence4B3A4_coeff_79
  recurrence4B3A4_coeff_8
  recurrence4B3A4_coeff_80
  recurrence4B3A4_coeff_81
  recurrence4B3A4_coeff_82
  recurrence4B3A4_coeff_83
  recurrence4B3A4_coeff_84
  recurrence4B3A4_coeff_85
  recurrence4B3A4_coeff_86
  recurrence4B3A4_coeff_87
  recurrence4B3A4_coeff_88
  recurrence4B3A4_coeff_89
  recurrence4B3A4_coeff_9
  recurrence4B3A4_coeff_90
  recurrence4B3A4_coeff_91
  recurrence4B3A4_coeff_92
  recurrence4B3A4_coeff_93
  recurrence4B3A4_coeff_94
  recurrence4B3A4_coeff_95

attribute [local simp]
  recurrence4B3A4_coeff_96
  recurrence4B3A4_coeff_97
  recurrence4B3A4_coeff_98
  recurrence4B3A4_coeff_99

private theorem recurrence4Scalar1First_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (171 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_171 :
    recurrence4Scalar1First.coeff 171 =
      -(((((135851151 * 10 ^ 70 +
        3681986263210794371321482758297520431852106739623602025365695588165192) * 10 ^ 70 +
        3088362179505623758555364832568177277822306972258142360073155917798973) * 10 ^ 70 +
        3109216020005323792437800852112591466580451043077332639970130655302907) * 10 ^ 70 +
        9271922760447754261861729191401576160077636974540657330342817885984543) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 172,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (171 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_171_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (172 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_172 :
    recurrence4Scalar1First.coeff 172 =
      (((((422290042 * 10 ^ 70 +
        1072176701546716894249742457200762705819092456669683835400417781142797) * 10 ^ 70 +
        6642153390956606320834043838483385303535836800720047150686962990698688) * 10 ^ 70 +
        1148002228939720803046565953295966268658528776388134706828328147690187) * 10 ^ 70 +
        4334490019907738123436470601785847484555000251662908933519417718197377) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 173,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (172 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_172_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (173 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_173 :
    recurrence4Scalar1First.coeff 173 =
      -(((((1293066748 * 10 ^ 70 +
        0233465015773742104059602332909509834630411209265296687633359353266636) * 10 ^ 70 +
        5389864919052559177914179451308368639727496502966770237728434970703492) * 10 ^ 70 +
        4342690370634074859667510748375439309594485144388148639562001049389753) * 10 ^ 70 +
        5988582753317415963714038911144653964942642965474066805728277253855147) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 174,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (173 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_173_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (174 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_174 :
    recurrence4Scalar1First.coeff 174 =
      (((((3900488674 * 10 ^ 70 +
        2732985969679051383665031076411744380520925219939736176064433079127915) * 10 ^ 70 +
        0989645179466554328585740553529441086819286965232914181057573761108393) * 10 ^ 70 +
        2921445234473916457896710747484123026523214024765909791588268049301996) * 10 ^ 70 +
        2775220434212820903785961703655738433575325042879119573471692764437327) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 175,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (174 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_174_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (175 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_175 :
    recurrence4Scalar1First.coeff 175 =
      -(((((11591235739 * 10 ^ 70 +
        1954660103767071732430574630094607362913834432101655105875179633824751) * 10 ^ 70 +
        1295841936011376085300321699106833157186487836983646156494566741914064) * 10 ^ 70 +
        5911940633028365086367521329110134605498213541878681363916117473445592) * 10 ^ 70 +
        7194806165816731980704119374435783473315991010943548055274503215257992) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 176,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (175 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_175_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (176 - x) (by
      omega)]
    norm_num

theorem recurrence4Scalar1First_coeff_176 :
    recurrence4Scalar1First.coeff 176 =
      (((((33937281681 * 10 ^ 70 +
        6835401934908190138424293389467602874197820281955994183078423549590819) * 10 ^ 70 +
        4923709904550079296857166329678082016355580650723427793801475913923944) * 10 ^ 70 +
        3740380008778362588505018468235171475704036212996877611389712025104349) * 10 ^ 70 +
        9691080587293483358213270799209694161714157450643079491247771380609572) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 177,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (176 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_176_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (177 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_177_suffix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (177 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_177 :
    recurrence4Scalar1First.coeff 177 =
      -(((((97900346570 * 10 ^ 70 +
        4446050791243477048043142775060441946288839219832668312174287721905840) * 10 ^ 70 +
        4707851360078592047545153834739109395078894848292129059765489200283407) * 10 ^ 70 +
        1670933473124150027138054474060045877182206894852596977825636670457015) * 10 ^ 70 +
        9090562869424232629694275562520041431934340750873909828735280793802597) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 178,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (177 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_177_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_177_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (178 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_178_suffix_zero :
    (∑ x ∈ Finset.range 2,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (178 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_178 :
    recurrence4Scalar1First.coeff 178 =
      (((((278274781993 * 10 ^ 70 +
        7700689989526234968563968441071012019000732798089374569195313721162090) * 10 ^ 70 +
        0096562167067024397976900333112155919602960884571075637311823234406331) * 10 ^ 70 +
        3637747784009816712917399258524340844123225179540373387064874326697438) * 10 ^ 70 +
        3628934555611166207755804043411307501951768772810312269188296800003979) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 179,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (178 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_178_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_178_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (179 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_179_suffix_zero :
    (∑ x ∈ Finset.range 3,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (179 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_179 :
    recurrence4Scalar1First.coeff 179 =
      -(((((779413344448 * 10 ^ 70 +
        4732322457987265933835071646618954507405923834425753523320322626862099) * 10 ^ 70 +
        9683507343240732449425897197496999312608143604493978835011104719225372) * 10 ^ 70 +
        8757621855915839113553346523511441213010584933451966189129374867474520) * 10 ^ 70 +
        1092209574089648339212852355043746823852861142312885908472118970245146) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 180,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (179 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_179_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_179_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (180 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_180_suffix_zero :
    (∑ x ∈ Finset.range 4,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (180 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_180 :
    recurrence4Scalar1First.coeff 180 =
      (((((2151233001549 * 10 ^ 70 +
        2935860737686217364812920859509109335194392508693488023861583223414480) * 10 ^ 70 +
        9755361559485750238411072516771344914942937381025632666125320736056186) * 10 ^ 70 +
        5272370994637720388963394992470032147338682100861557326214911988598884) * 10 ^ 70 +
        1453590975483442109170640154714602228670489375498535863254248278564978) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 181,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (180 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_180_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_180_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (181 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_181_suffix_zero :
    (∑ x ∈ Finset.range 5,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (181 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_181 :
    recurrence4Scalar1First.coeff 181 =
      -(((((5851312838593 * 10 ^ 70 +
        5850224295702552725859138252682709078590580683011665284240276327311081) * 10 ^ 70 +
        4784930939726539773147647089551965797407274591627565376853654635083628) * 10 ^ 70 +
        4929075994824704256871409413612464614443196845267179658142161938610141) * 10 ^ 70 +
        8380600965920076064732878779205960823608779764505183795638804918734810) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 182,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (181 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_181_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_181_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (182 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_182_suffix_zero :
    (∑ x ∈ Finset.range 6,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (182 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_182 :
    recurrence4Scalar1First.coeff 182 =
      (((((15685032771702 * 10 ^ 70 +
        7025273816010111746568542112520324919917364186791850624974082777602057) * 10 ^ 70 +
        3481029948891754361419504468391585018718317415850711798231478869517957) * 10 ^ 70 +
        9616001733243212643200452647956681717988630880499389713787595515527102) * 10 ^ 70 +
        6809651503678702425434302383329606745745231284586170185318198751461377) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 183,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (182 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_182_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_182_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (183 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_183_suffix_zero :
    (∑ x ∈ Finset.range 7,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (183 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_183 :
    recurrence4Scalar1First.coeff 183 =
      -(((((41438417733529 * 10 ^ 70 +
        1167653932313925289521551919916351351715983773799394916239059252024274) * 10 ^ 70 +
        1055995967303662398653341260983362081814135473122790258314519886741033) * 10 ^ 70 +
        4163651088875645653524875367373858250666906025812611511070393350418280) * 10 ^ 70 +
        9120256911927318340666894523513908347080546206321021488150278612946950) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 184,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (183 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_183_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_183_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (184 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_184_suffix_zero :
    (∑ x ∈ Finset.range 8,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (184 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_184 :
    recurrence4Scalar1First.coeff 184 =
      (((((107900954713152 * 10 ^ 70 +
        2427771939194967253863948897340729123888699588916326886100923582829388) * 10 ^ 70 +
        0568894380543429325648287218623033867693656969190777249860365306304676) * 10 ^ 70 +
        3338713644274650595905388066421147367163935024642760375747080290835942) * 10 ^ 70 +
        3752387442473375995926157479417513449331219523439174443077200267253424) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 185,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (184 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_184_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_184_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (185 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_185_suffix_zero :
    (∑ x ∈ Finset.range 9,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (185 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_185 :
    recurrence4Scalar1First.coeff 185 =
      -(((((276929977771980 * 10 ^ 70 +
        1474198741341771851814123779600993584695193600593671774783310481209124) * 10 ^ 70 +
        8425867855945659804387149709051791788987188929280225910062226709144165) * 10 ^ 70 +
        3525926022711466853222283255563085004149481978904880343828843305325846) * 10 ^ 70 +
        6516984290707410347831318635273753678849878715618059373815573688768859) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 186,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (185 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_185_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_185_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (186 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_186_suffix_zero :
    (∑ x ∈ Finset.range 10,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (186 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_186 :
    recurrence4Scalar1First.coeff 186 =
      (((((700575261585975 * 10 ^ 70 +
        9575795399653563853105780828564645300780321096104704074878505819924899) * 10 ^ 70 +
        0162543756326233040682245400385684523185699658665422319288129341067627) * 10 ^ 70 +
        3012849642238596006367043189388800953037696439224876689210504509066211) * 10 ^ 70 +
        9314507003633893324887566900918509293972278210544930542829465238894805) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 187,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (186 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_186_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_186_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (187 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_187_suffix_zero :
    (∑ x ∈ Finset.range 11,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (187 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_187 :
    recurrence4Scalar1First.coeff 187 =
      -(((((1747015557004493 * 10 ^ 70 +
        8630085553813802971767744421067465699162362985844448071424115987820986) * 10 ^ 70 +
        5727551247289056416480100713417730018216639660176529191782168570685817) * 10 ^ 70 +
        7521095654583305366975047500904199260390033150761654324653798544355228) * 10 ^ 70 +
        5452944840950579034534926791422161707127959702402120581283187489346099) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 188,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (187 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_187_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_187_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (188 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_188_suffix_zero :
    (∑ x ∈ Finset.range 12,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (188 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_188 :
    recurrence4Scalar1First.coeff 188 =
      (((((4294497257063664 * 10 ^ 70 +
        6427655920440983916358587639694314852428011549345774277274149285243887) * 10 ^ 70 +
        6013141236696029898407804463983478886377374279354763303014816568191278) * 10 ^ 70 +
        9194639002758329169821371672141507038074980683928356671615242537126996) * 10 ^ 70 +
        7071079133563826991933294484089814368690842561071800397026565668099348) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 189,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (188 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_188_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_188_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (189 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_189_suffix_zero :
    (∑ x ∈ Finset.range 13,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (189 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_189 :
    recurrence4Scalar1First.coeff 189 =
      -(((((10406803217990090 * 10 ^ 70 +
        4802091144601435379809564117109946441727382924578630835709765030865428) * 10 ^ 70 +
        5552987871547288451148732068861132656361487123150555984373361290080098) * 10 ^ 70 +
        4245016619841601549275276821139742999019736535691552945972697913464251) * 10 ^ 70 +
        6162823181040956696050354158953096635542851599949159647953919676759152) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 190,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (189 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_189_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_189_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (190 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_190_suffix_zero :
    (∑ x ∈ Finset.range 14,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (190 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_190 :
    recurrence4Scalar1First.coeff 190 =
      (((((24861488653187426 * 10 ^ 70 +
        1966382546733631671494028345893775190629886325186474727456086013675421) * 10 ^ 70 +
        7382242325155037333639449158901008041882681458594332117087521713334627) * 10 ^ 70 +
        9389799969257232177533692118508341203127088543331478921875499425571874) * 10 ^ 70 +
        4337436660020009602581733990351080720071396209619240802156585696411268) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 191,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (190 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_190_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_190_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (191 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_191_suffix_zero :
    (∑ x ∈ Finset.range 15,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (191 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_191 :
    recurrence4Scalar1First.coeff 191 =
      -(((((58553985740501803 * 10 ^ 70 +
        5667931967761565100041024899423227320390530673519468370446214285708901) * 10 ^ 70 +
        9187410376320936789320025825459670003927985563921783294945680842591615) * 10 ^ 70 +
        5324884071665071698502658313149081619823184949155877004375265853488360) * 10 ^ 70 +
        3176644257629013693917657765819841811533799758524586117436199706494408) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 192,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (191 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_191_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_191_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (192 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_192_suffix_zero :
    (∑ x ∈ Finset.range 16,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (192 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_192 :
    recurrence4Scalar1First.coeff 192 =
      (((((135962634781455160 * 10 ^ 70 +
        3236698951653050396572038117897133686654127257666767908910246078896329) * 10 ^ 70 +
        9096492740513673004218450160538986254716815663478159239656582050902240) * 10 ^ 70 +
        9997511999584352128968559727730449090579969552596282903424701571744049) * 10 ^ 70 +
        9956507964827658024875969532681961306124699004535511035973268845889388) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 193,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (192 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_192_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_192_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (193 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_193_suffix_zero :
    (∑ x ∈ Finset.range 17,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (193 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_193 :
    recurrence4Scalar1First.coeff 193 =
      -(((((311264902890719023 * 10 ^ 70 +
        3598747678013617534548313839330871931360304369387935259092441028946199) * 10 ^ 70 +
        4585657739979298929788212785558082308503118820136171696399258626740260) * 10 ^ 70 +
        9029825123434898097207573679044886785808198164379078554443780893494729) * 10 ^ 70 +
        9777894656937315663108869837572048225086026808803357266755735640031491) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 194,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (193 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_193_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_193_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (194 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_194_suffix_zero :
    (∑ x ∈ Finset.range 18,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (194 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_194 :
    recurrence4Scalar1First.coeff 194 =
      (((((702589046413626003 * 10 ^ 70 +
        5566915832486472737711402593051991625044888288770245707444264489693764) * 10 ^ 70 +
        4488360188817998853029644968125742644755300290215102070702151637856371) * 10 ^ 70 +
        2559897947631695358030984480795498447581310188015239160247650456569268) * 10 ^ 70 +
        7949323768207403637624151762836519057644309322181073517730660844214940) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 195,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (194 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_194_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_194_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (195 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_195_suffix_zero :
    (∑ x ∈ Finset.range 19,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (195 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_195 :
    recurrence4Scalar1First.coeff 195 =
      -(((((1563672779234375683 * 10 ^ 70 +
        9322552589353495236967240066505364533155617971290833106602155846719498) * 10 ^ 70 +
        7121187569757267241628592960289449754101067070818536766110113602610255) * 10 ^ 70 +
        9580259337969740833782353894541812651354374422186351414667385525317613) * 10 ^ 70 +
        4765112583013603830689156211057054925155381698824680081344482046541323) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 196,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (195 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_195_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_195_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (196 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_196_suffix_zero :
    (∑ x ∈ Finset.range 20,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (196 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_196 :
    recurrence4Scalar1First.coeff 196 =
      (((((3431435014542201213 * 10 ^ 70 +
        4155545215474997906541607316256131253260549566529224970556446603779149) * 10 ^ 70 +
        9616378915602223535909845993805372921483510512923533511674870857281276) * 10 ^ 70 +
        1463858528609511942006643471125828086801540255465850074386389780738256) * 10 ^ 70 +
        1864150898790314080861641627918957336296930007626841817477372950198813) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 197,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (196 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_196_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_196_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (197 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_197_suffix_zero :
    (∑ x ∈ Finset.range 21,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (197 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_197 :
    recurrence4Scalar1First.coeff 197 =
      -(((((7425106481910103350 * 10 ^ 70 +
        8148415587514193057713996753343594990417195959997049286630948213001408) * 10 ^ 70 +
        8471167944279775497112834024309832657037560399141735068245602995612111) * 10 ^ 70 +
        2189581574896615496823782461611931536125571516287835310271346170952460) * 10 ^ 70 +
        8309309190227568008168958305015516095747213363329671781890517041811655) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 198,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (197 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_197_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_197_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (198 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_198_suffix_zero :
    (∑ x ∈ Finset.range 22,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (198 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_198 :
    recurrence4Scalar1First.coeff 198 =
      (((((15843009702529374255 * 10 ^ 70 +
        0835612248246590524001273085091551047565801536260042183004386457994268) * 10 ^ 70 +
        0424162461775045746701390933467136581765413771942600600355858724873108) * 10 ^ 70 +
        3973317394425782688851910347452353742204986196205513037174665633563571) * 10 ^ 70 +
        2261927618082252434783031835329176736605357035497726937336411133595967) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 199,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (198 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_198_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_198_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (199 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_199_suffix_zero :
    (∑ x ∈ Finset.range 23,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (199 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_199 :
    recurrence4Scalar1First.coeff 199 =
      -(((((33334301687612012598 * 10 ^ 70 +
        7153394288145621001811861761630609588609653815052690355934976521470271) * 10 ^ 70 +
        9077198868342161173744342309482761886848307453643405632536457405532762) * 10 ^ 70 +
        6665219391368310357522549035225556409023818390124540098626364548973682) * 10 ^ 70 +
        5597718022458215720073556556255481086976118306638713716044482485252948) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 200,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (199 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_199_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_199_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (200 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_200_suffix_zero :
    (∑ x ∈ Finset.range 24,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (200 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_200 :
    recurrence4Scalar1First.coeff 200 =
      (((((69162992013725486778 * 10 ^ 70 +
        7756566933852577513412089742390106979180457166946265114085674063678364) * 10 ^ 70 +
        2182981612602822056967852455816096354801958338370186557036259789478744) * 10 ^ 70 +
        8117242593685909066199204581960812504812984209115036986394117976589920) * 10 ^ 70 +
        2569110226730788933610985612430772090827253438110234275244760542728674) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 201,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (200 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_200_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_200_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (201 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_201_suffix_zero :
    (∑ x ∈ Finset.range 25,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (201 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_201 :
    recurrence4Scalar1First.coeff 201 =
      -(((((141512393825663658579 * 10 ^ 70 +
        4059900639919335065841784821339120637312414353455290149087232163648606) * 10 ^ 70 +
        4373279447321892968254007253353689077408169964916495507114207778411929) * 10 ^ 70 +
        5023389649983583419794705813168908671254394090135383640139744248884863) * 10 ^ 70 +
        8177318517578168852083281128265783582613421786702720028330308915984648) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 202,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (201 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_201_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_201_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (202 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_202_suffix_zero :
    (∑ x ∈ Finset.range 26,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (202 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_202 :
    recurrence4Scalar1First.coeff 202 =
      (((((285537085211416321276 * 10 ^ 70 +
        4250663156103682285074148271592959076094808570621570019250314000753036) * 10 ^ 70 +
        9984512621594407520702740623171821428448303692373476032500893161776298) * 10 ^ 70 +
        3787090572514745961721323117325822950932898512777357213084451914996899) * 10 ^ 70 +
        6058345130923412899311852941373531142574083511003210124014062542000738) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 203,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (202 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_202_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_202_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (203 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_203_suffix_zero :
    (∑ x ∈ Finset.range 27,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (203 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_203 :
    recurrence4Scalar1First.coeff 203 =
      -(((((568180651248590433424 * 10 ^ 70 +
        2169080884497708384941028582010690459461635149855557133914139343805791) * 10 ^ 70 +
        1314114416032038382535620414888637229511334705838490384678112762353331) * 10 ^ 70 +
        3550975483848603310434204076026410262844344578220234521931609013545836) * 10 ^ 70 +
        0509738787623754719090646376222656831153033053910234971871232197930007) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 204,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (203 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_203_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_203_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (204 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_204_suffix_zero :
    (∑ x ∈ Finset.range 28,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (204 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_204 :
    recurrence4Scalar1First.coeff 204 =
      (((((1114998425139320226494 * 10 ^ 70 +
        8337043065109263196374911590663675985264720548219682995644552050585927) * 10 ^ 70 +
        4111124591959224235748530375161374327884443986801838273280283945138105) * 10 ^ 70 +
        6581091687556004860744946817387858645426308849616523338262263249589659) * 10 ^ 70 +
        5735703365025071481327924887771289143131602499555046872667754293992867) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 205,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (204 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_204_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_204_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (205 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_205_suffix_zero :
    (∑ x ∈ Finset.range 29,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (205 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_205 :
    recurrence4Scalar1First.coeff 205 =
      -(((((2157910700345712403562 * 10 ^ 70 +
        8329109498125884669191913650405048585086583230082081771451022694333105) * 10 ^ 70 +
        6664264995501783522071238094164257144619026557860775576954134687070718) * 10 ^ 70 +
        4264736567553358220840848081697566706673228606419944762762514514587603) * 10 ^ 70 +
        1407086369696016266323280201282330190014070638634395375154042660649153) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 206,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (205 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_205_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_205_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (206 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_206_suffix_zero :
    (∑ x ∈ Finset.range 30,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (206 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_206 :
    recurrence4Scalar1First.coeff 206 =
      (((((4118803466226056535843 * 10 ^ 70 +
        3692195948456040283220253524865936912241726721866362136825412262339912) * 10 ^ 70 +
        5290820642441706580653461585101276817951795831144295990625344437453951) * 10 ^ 70 +
        2078347395051221401194396187963561029937110253685162839104476454722495) * 10 ^ 70 +
        3274728423019557531654384838733680471653935356095803998789127965725640) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 207,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (206 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_206_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_206_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (207 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_207_suffix_zero :
    (∑ x ∈ Finset.range 31,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (207 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_207 :
    recurrence4Scalar1First.coeff 207 =
      -(((((7753423706953786209375 * 10 ^ 70 +
        4447905297642123372333043171097145167930772301788916984953715867688006) * 10 ^ 70 +
        2944408324347190167572832683473900660718577181666403110282047800279844) * 10 ^ 70 +
        9933086756563556681931778796226051437329005245225239856624333528786242) * 10 ^ 70 +
        1360311936430006002283408969881127527262602438831605609202164415694934) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 208,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (207 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_207_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_207_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (208 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_208_suffix_zero :
    (∑ x ∈ Finset.range 32,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (208 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_208 :
    recurrence4Scalar1First.coeff 208 =
      (((((14394836724349028518315 * 10 ^ 70 +
        5078142887257631002490189960731920957057170453817432644320122339962888) * 10 ^ 70 +
        9422631237982095985226101382985925490050646008415982261434095898111882) * 10 ^ 70 +
        8767029387512814207638862511601535260472210300356104390028248286231797) * 10 ^ 70 +
        2821431408514861896436841404807996838600509031543837445260912277519619) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 209,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (208 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_208_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_208_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (209 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_209_suffix_zero :
    (∑ x ∈ Finset.range 33,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (209 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_209 :
    recurrence4Scalar1First.coeff 209 =
      -(((((26358223551158121310795 * 10 ^ 70 +
        5677147455065166854944402779264837935433909628885187965654957775463830) * 10 ^ 70 +
        1379600728930662143872075649521005952153377156385362434274034891194666) * 10 ^ 70 +
        5750869517898195837189321076841718124642613579705118386470937340592713) * 10 ^ 70 +
        0870967270134207401879408034922584285888370402382504726397148954168197) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 210,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (209 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_209_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_209_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (210 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_210_suffix_zero :
    (∑ x ∈ Finset.range 34,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (210 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_210 :
    recurrence4Scalar1First.coeff 210 =
      (((((47602147238673567794890 * 10 ^ 70 +
        1917322907208195451032503019419653341756829544734890765204944633657743) * 10 ^ 70 +
        7558646007452475139548184462989062447809353631327843553575927545894958) * 10 ^ 70 +
        7109265099024426912010325896549101085724155535589463958718763195991398) * 10 ^ 70 +
        5399795912926250926466965976232126848934830415831435481226700988483682) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 211,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (210 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_210_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_210_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (211 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_211_suffix_zero :
    (∑ x ∈ Finset.range 35,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (211 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_211 :
    recurrence4Scalar1First.coeff 211 =
      -(((((84789533949811727781215 * 10 ^ 70 +
        3036235528233401546342328036451519396462276739458704363978119786989721) * 10 ^ 70 +
        0818832244228324222130314437716364587539664462882722097609503268450728) * 10 ^ 70 +
        1448532652729514493102069414268928443399878340360592631366414362711095) * 10 ^ 70 +
        5472145276336242426679485969676089341547830304672509925047415666638353) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 212,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (211 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_211_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_211_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (212 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_212_suffix_zero :
    (∑ x ∈ Finset.range 36,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (212 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_212 :
    recurrence4Scalar1First.coeff 212 =
      (((((148959075222915528934275 * 10 ^ 70 +
        4410881501877180725354112142126611506419551767742990648005575380454373) * 10 ^ 70 +
        5415193526723876553745283571474983062541867889457080652290819511755373) * 10 ^ 70 +
        4253750994136186876790784935598780057960073131056917806488763837624698) * 10 ^ 70 +
        0745730301035589178816699836391204993622836671067407265345232066909014) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 213,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (212 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_212_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_212_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (213 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_213_suffix_zero :
    (∑ x ∈ Finset.range 37,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (213 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_213 :
    recurrence4Scalar1First.coeff 213 =
      -(((((258109406867856764386401 * 10 ^ 70 +
        8419542223847257148016540875075190865985050716751840844550557483522336) * 10 ^ 70 +
        6808232885269325125476937959903188567931967577112250811077316508543917) * 10 ^ 70 +
        4533937349739316406919375039320482502131969406614825153628213165814374) * 10 ^ 70 +
        1400299585052137665273333768582429102786474614604799673192292116308951) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 214,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (213 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_213_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_213_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (214 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_214_suffix_zero :
    (∑ x ∈ Finset.range 38,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (214 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_214 :
    recurrence4Scalar1First.coeff 214 =
      (((((441118605010206421256039 * 10 ^ 70 +
        9476497768043720733965181925133907422711641638424650580927576980913688) * 10 ^ 70 +
        9031567334340886287214223287704914827216073473426153352847359273977940) * 10 ^ 70 +
        2710548659634389419084194291144361318348590463812259075627201043680456) * 10 ^ 70 +
        3075042515355827747322629101928720758195177740047450973183125372690592) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 215,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (214 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_214_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_214_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (215 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_215_suffix_zero :
    (∑ x ∈ Finset.range 39,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (215 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_215 :
    recurrence4Scalar1First.coeff 215 =
      -(((((743572820632406725470654 * 10 ^ 70 +
        9347688232133876312025395233434880858502418269381622725547419326139513) * 10 ^ 70 +
        8571053292419865147629763134346079722124900453766896701667157429104730) * 10 ^ 70 +
        5618964263627169042682797882327533074607936877498933765201785671999459) * 10 ^ 70 +
        4988516215061708092547620300645084768195079591411403390276076365455591) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 216,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (215 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_215_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_215_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (216 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_216_suffix_zero :
    (∑ x ∈ Finset.range 40,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (216 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_216 :
    recurrence4Scalar1First.coeff 216 =
      (((((1236259092293616667992201 * 10 ^ 70 +
        8856047240483839263773531247019754097980998740208195113278048298252069) * 10 ^ 70 +
        2325105735243752514055846294827643139216798452160178310749457772186698) * 10 ^ 70 +
        7630310159147785572149741197907290119013214994546011076376968946205036) * 10 ^ 70 +
        6429133691263442392254369015050658947603711335355512101823123702855946) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 217,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (216 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_216_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_216_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (217 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_217_suffix_zero :
    (∑ x ∈ Finset.range 41,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (217 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_217 :
    recurrence4Scalar1First.coeff 217 =
      -(((((2027281033799867708117233 * 10 ^ 70 +
        4517653953344951368427036983446655993634560530586621314918850220840373) * 10 ^ 70 +
        0370765166673595523057060010749160079061054635330351204130716441451318) * 10 ^ 70 +
        6377752752965198500985620132457750129503656230097126068464282155860234) * 10 ^ 70 +
        7470791157742357584129565248708285121657478103509922974579147990040252) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 218,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (217 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_217_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_217_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (218 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_218_suffix_zero :
    (∑ x ∈ Finset.range 42,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (218 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_218 :
    recurrence4Scalar1First.coeff 218 =
      (((((3278965120535623222298113 * 10 ^ 70 +
        0624760066741848331722925969358026262573988774011544112574496360709298) * 10 ^ 70 +
        2630835380497655124604608112781839603233443269766172630438036946130127) * 10 ^ 70 +
        9983106603416729423521459264019984638053410087072775543819015390984469) * 10 ^ 70 +
        7448099927087610518330462955069106047180983330973613327821819154010914) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 219,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (218 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_218_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_218_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (219 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_219_suffix_zero :
    (∑ x ∈ Finset.range 43,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (219 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_219 :
    recurrence4Scalar1First.coeff 219 =
      -(((((5230909518449981966126054 * 10 ^ 70 +
        5506344868682560512198757002831765339931014729734917962239657745302223) * 10 ^ 70 +
        0530493986927799897643667095989122704780095115937898271194734294175688) * 10 ^ 70 +
        5604260250264995813447078648384060848799623373231071249477078944380358) * 10 ^ 70 +
        0843981271324311078394040193921590663432001661109376307608722563981889) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 220,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (219 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_219_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_219_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (220 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_220_suffix_zero :
    (∑ x ∈ Finset.range 44,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (220 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_220 :
    recurrence4Scalar1First.coeff 220 =
      (((((8230640278539872528873172 * 10 ^ 70 +
        6528998960052696224039407760368809716286586559555937854340834037447526) * 10 ^ 70 +
        8447403750929803097131393508853099230036872207194169143202079776659464) * 10 ^ 70 +
        1614468452846729616814974884821041607968051475529134691317789990845611) * 10 ^ 70 +
        7301292119497364719172059179771076594808760698876441019032257523944085) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 221,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (220 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_220_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_220_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (221 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_221_suffix_zero :
    (∑ x ∈ Finset.range 45,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (221 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_221 :
    recurrence4Scalar1First.coeff 221 =
      -(((((12773316344352990734577432 * 10 ^ 70 +
        4758077973340417394384067339568269755576082091376230481749701383613599) * 10 ^ 70 +
        8596139948728858378027561449881448054672165960195792301448299896846593) * 10 ^ 70 +
        8907886366472433673329752853153755454652203295609535964411567671657575) * 10 ^ 70 +
        9137825926429224584505474845702799516153184295287544502304383823405882) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 222,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (221 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_221_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_221_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (222 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_222_suffix_zero :
    (∑ x ∈ Finset.range 46,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (222 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_222 :
    recurrence4Scalar1First.coeff 222 =
      (((((19551682401096539805108202 * 10 ^ 70 +
        3020328077590498408786458048121708490044026311241068217616115392595486) * 10 ^ 70 +
        2734252200135278105088762687151956131124582791865678607148072542162262) * 10 ^ 70 +
        2113079938483212537816543778453901860440113705653224550990112793173134) * 10 ^ 70 +
        0921750210529800875517885968120697476927544348356037164992583873662820) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 223,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (222 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_222_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_222_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (223 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_223_suffix_zero :
    (∑ x ∈ Finset.range 47,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (223 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_223 :
    recurrence4Scalar1First.coeff 223 =
      -(((((29516911021773660894004966 * 10 ^ 70 +
        4213595571684149325216706461036520313658733355322176508627476912263164) * 10 ^ 70 +
        6496887489100786076354623243522551748398242593338918363253911616812390) * 10 ^ 70 +
        0295892606678927358489044441415508210379010120331745398510065631756198) * 10 ^ 70 +
        4220078484948160335016768397861695547140927997857466546558025590593201) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 224,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (223 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_223_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_223_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (224 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_224_suffix_zero :
    (∑ x ∈ Finset.range 48,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (224 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_224 :
    recurrence4Scalar1First.coeff 224 =
      (((((43950003556407378874174338 * 10 ^ 70 +
        1169039051941170832449939225651477394037465847425348471519391333286399) * 10 ^ 70 +
        7881028558131970201669554763515493807832746132665455324918429902985868) * 10 ^ 70 +
        4252146155590442433443481487181932022934024065819166380193301900613114) * 10 ^ 70 +
        5433633950877201749630271146166216735239598385738150598900816042634987) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 225,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (224 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_224_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_224_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (225 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (225 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_225 :
    recurrence4Scalar1First.coeff 225 =
      -(((((64541947212064804284985087 * 10 ^ 70 +
        3888780624170995419394473941017944044716846961716154741615770968618896) * 10 ^ 70 +
        1448400349455667214060019717877197785731807161306389707533296445929498) * 10 ^ 70 +
        6971213307936477717240400481675102744067187509581695364235322837003488) * 10 ^ 70 +
        5785224890993965345170415086493975579661020270252042817936632165185275) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (225 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_225_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (226 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (226 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_226 :
    recurrence4Scalar1First.coeff 226 =
      (((((93478805857438938102373037 * 10 ^ 70 +
        8298994580452925075281092274579954137936413915519562661063047481442298) * 10 ^ 70 +
        7241888430549360625400301112745076780190289219593644920407231885812851) * 10 ^ 70 +
        7683709356066247287806159147504275557970763593356697986282795153448776) * 10 ^ 70 +
        6640424562473584077918401532921152931078547782739887122642958896877478) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (226 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_226_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (227 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (227 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_227 :
    recurrence4Scalar1First.coeff 227 =
      -(((((133525373586590052250626282 * 10 ^ 70 +
        0669701496391105286251607371962454292764881501906609040995845688465504) * 10 ^ 70 +
        5798252407778596961718633232145088051119173365692654058195860862037379) * 10 ^ 70 +
        4904471792789886342164408201248139106228606622079694942014481993678384) * 10 ^ 70 +
        5965900045692342730387737961827040968758809156107738688644566989876912) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (227 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_227_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (228 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (228 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_228 :
    recurrence4Scalar1First.coeff 228 =
      (((((188098061634133194861006525 * 10 ^ 70 +
        7433335736821554209262450602212645629709755752432296816222773104827802) * 10 ^ 70 +
        0916908750903497340251934004136293643735975647837669384206857897621702) * 10 ^ 70 +
        0052566224579221956411280272712759269789103919518108921625825284158912) * 10 ^ 70 +
        0471100649963760275929236250495237135732776816784562398686259265146392) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (228 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_228_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (229 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (229 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_229 :
    recurrence4Scalar1First.coeff 229 =
      -(((((261314567626293837765102530 * 10 ^ 70 +
        7856516667248460060569777889031383836835467263709380633422030803651505) * 10 ^ 70 +
        1913395498052068180178893486646782268879513113821828587162064828295121) * 10 ^ 70 +
        2302300779930100974389215305590737492756363275778493049802667081824606) * 10 ^ 70 +
        9997427806090799387130136321579110484413043280815773473783360604909133) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (229 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_229_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (230 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (230 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_230 :
    recurrence4Scalar1First.coeff 230 =
      (((((358004984048076741813311510 * 10 ^ 70 +
        6215284638400220934576908199706229875150597997606179026385597706364350) * 10 ^ 70 +
        7621280359307203005615533714460624339932964631011763894448206688539955) * 10 ^ 70 +
        1080727308062355902216675721376978932228753495229668497931790398186246) * 10 ^ 70 +
        8032191427751656154331856829963704454704635873996133915632916089458492) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (230 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_230_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (231 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (231 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_231 :
    recurrence4Scalar1First.coeff 231 =
      -(((((483666876250737660448376761 * 10 ^ 70 +
        8870789249547042757719879056556037806055833136733352178422171589994352) * 10 ^ 70 +
        9270269824543773587792667543001979873539657841659252934798850273308634) * 10 ^ 70 +
        1896573060991148651395871966428623369900216999785135126330420411578354) * 10 ^ 70 +
        1797949518642136938981639112648369827001094822987811993628891836130972) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (231 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_231_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (232 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (232 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_232 :
    recurrence4Scalar1First.coeff 232 =
      (((((644346146950386524202914904 * 10 ^ 70 +
        7245474966327081116184308987983383890408827041391226677377436442190360) * 10 ^ 70 +
        9001224577476182290299086946255473883052610148859157464245327728216968) * 10 ^ 70 +
        9092282368631163201004402165568542939532422773764267972763065599493435) * 10 ^ 70 +
        6246344219232762982845930390309408053406954986572546182241330329583664) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (232 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_232_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (233 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (233 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_233 :
    recurrence4Scalar1First.coeff 233 =
      -(((((846426895636307000964221907 * 10 ^ 70 +
        8283968740059399006085339830888238752326648350784590710427397129508107) * 10 ^ 70 +
        5157212520378614230072807895449579759157193654738583378925109520937581) * 10 ^ 70 +
        4482461558807404189221403490551658311691431986466034541738605216875083) * 10 ^ 70 +
        3251056314872533645763542276694257887525613403122829278990115574971244) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (233 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_233_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (234 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (234 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_234 :
    recurrence4Scalar1First.coeff 234 =
      (((((1096317608605232194332928995 * 10 ^ 70 +
        4788326343869734501910986949682955755783227137546354844924681206365252) * 10 ^ 70 +
        1023082846606087350623868978773914875081891225755195015531838764514820) * 10 ^ 70 +
        4373636841715159249448444939182554703609464467141947875513891859084572) * 10 ^ 70 +
        0220736876885143715270734014980936091380841811961902626361284483313606) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (234 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_234_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (235 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (235 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_235 :
    recurrence4Scalar1First.coeff 235 =
      -(((((1400028313334491609122767176 * 10 ^ 70 +
        6848436608022361166776803405316080667034651647953007616908353017050725) * 10 ^ 70 +
        5748266588165037966538737433641481473575215131825772371376424944596357) * 10 ^ 70 +
        5014666009888416925494524144286441242023983650696265242385128754543796) * 10 ^ 70 +
        0500276957192026021147639936527715383027734150733084225027464267120314) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (235 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_235_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (236 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (236 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_236 :
    recurrence4Scalar1First.coeff 236 =
      (((((1762643887908978951623873986 * 10 ^ 70 +
        7234953166487145273609995753021403750014528968389044677110748400985148) * 10 ^ 70 +
        3492746711501120635998502414854162738112781210289524566011552413925593) * 10 ^ 70 +
        4929821417064745069952375086984288475339031184671761872577530533679118) * 10 ^ 70 +
        3969321779670128272496393645560633551383201504778376778393324802795128) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (236 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_236_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (237 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (237 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_237 :
    recurrence4Scalar1First.coeff 237 =
      -(((((2187712133683711619593432222 * 10 ^ 70 +
        7656060696821869506618568346203864415817095012212827855463095089282872) * 10 ^ 70 +
        9820631787731017267545691159514339372165020396792678157021269921213339) * 10 ^ 70 +
        5285505839161289862501160693482952285967947533100892238498825911637027) * 10 ^ 70 +
        4041712213749888362471047054146049183438458901083567023340140046541010) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (237 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_237_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (238 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (238 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_238 :
    recurrence4Scalar1First.coeff 238 =
      (((((2676580513978655937314367902 * 10 ^ 70 +
        8696927318639285048355867228148873649540753030317403135037022054217678) * 10 ^ 70 +
        9391477870907487024152171686182606814233227634706698737443318068607137) * 10 ^ 70 +
        5638841241510671085006135763353049301245581231809399469737364829054278) * 10 ^ 70 +
        1915453775161934859188419776918155747406499460045811819046470756941287) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (238 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_238_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (239 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (239 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_239 :
    recurrence4Scalar1First.coeff 239 =
      -(((((3227731043988155101415960406 * 10 ^ 70 +
        9267967376683490755938258216908148131590287753571036639845183451512685) * 10 ^ 70 +
        6061130614836655513329641481710138199587928475842975426789771506100811) * 10 ^ 70 +
        2704890105601887313947649688551051901937283088649712583270884924649984) * 10 ^ 70 +
        1671601695671475643567280230923446758385314532633092986478291568114153) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (239 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_239_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (240 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (240 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_240 :
    recurrence4Scalar1First.coeff 240 =
      (((((3836176576352718740935007621 * 10 ^ 70 +
        2033700900573297715074049590529187028465481542543086962522293625949534) * 10 ^ 70 +
        0589543419766615143086202728510706384290393064062753828589822104365441) * 10 ^ 70 +
        9976093012821599190694313103787360749604159306232222572622040924522546) * 10 ^ 70 +
        8949614991711657612338672423003702959380234544983590025624982961139600) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (240 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_240_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (241 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (241 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_241 :
    recurrence4Scalar1First.coeff 241 =
      -(((((4492991236697845090274998636 * 10 ^ 70 +
        8692934174116923223772196584971945512074735130193608325896163544805573) * 10 ^ 70 +
        3892105685015092554901985260048559479080238383742242675501051693258104) * 10 ^ 70 +
        8903016785453196506919385250626137266426120057262209914056703742300290) * 10 ^ 70 +
        0289962809487420431954035720775884870791183301046732447120479740828968) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (241 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_241_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (242 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (242 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_242 :
    recurrence4Scalar1First.coeff 242 =
      (((((5185050604464932151159175161 * 10 ^ 70 +
        1342328235012965104898885116461010472845980226510181684849497045927349) * 10 ^ 70 +
        5170103669665768082462748767618349943941193539819476056040748288232448) * 10 ^ 70 +
        4603012325157853459967309564392837404690146963989679180520542637809309) * 10 ^ 70 +
        7725702774966731504458580792697621237937361826876039064884693987390538) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (242 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_242_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (243 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (243 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_243 :
    recurrence4Scalar1First.coeff 243 =
      -(((((5895051400854870232900026159 * 10 ^ 70 +
        4744426409171504460650565271138452522736293209496152385960797672272078) * 10 ^ 70 +
        4430698907148968525337334870806988930343053110682724781099976829482969) * 10 ^ 70 +
        1210899708108781648222232255612738968596724756229626275625236546397464) * 10 ^ 70 +
        3166187251122161279554138891174683526031156532391323967719287013723089) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (243 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_243_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (244 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (244 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_244 :
    recurrence4Scalar1First.coeff 244 =
      (((((6601864779547935753674617367 * 10 ^ 70 +
        1247151516748580960326162220832497884435334585163177016761999713968281) * 10 ^ 70 +
        3228425007744084407785416386608874779547587479042895518202532782068322) * 10 ^ 70 +
        1151344792653466549349652668561855580724784243394864514397384495405298) * 10 ^ 70 +
        2852435489896226566347132605029466924187143502008155282932417746209263) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (244 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_244_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (245 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (245 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_245 :
    recurrence4Scalar1First.coeff 245 =
      -(((((7281251889537006342187984515 * 10 ^ 70 +
        7109345873353377598702634139526589798636739434140155972376505533211976) * 10 ^ 70 +
        3727154934312585591710422374398222048485053354560620394606113824852972) * 10 ^ 70 +
        2491196767156807840170071337008258697489884464581440957821626065362024) * 10 ^ 70 +
        7398829619924422620438617505929689400605618058189798236835546433113866) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (245 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_245_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (246 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (246 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_246 :
    recurrence4Scalar1First.coeff 246 =
      (((((7906936742929217167586298428 * 10 ^ 70 +
        5590954004614168337576636492543114900001824691859248083856980602692119) * 10 ^ 70 +
        8603486857913188457814905735662563177322169406928999638324657787669021) * 10 ^ 70 +
        9544959459527424664266442699891493494713043460128854703873594527067568) * 10 ^ 70 +
        6799181640755247498473116520819606790208619571715431687176129106764957) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (246 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_246_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (247 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (247 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_247 :
    recurrence4Scalar1First.coeff 247 =
      -(((((8451992636338955042873255590 * 10 ^ 70 +
        7325118095196570865410978489885760845403532928748160602564515143398361) * 10 ^ 70 +
        6254643350064248685893396069844012002051007787381657768788102230033125) * 10 ^ 70 +
        4425743366151538832847239627217797588509372873575091558467316153101163) * 10 ^ 70 +
        9908923661140201465719246955740478308136419201649715929101492182849267) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (247 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_247_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (248 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (248 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_248 :
    recurrence4Scalar1First.coeff 248 =
      (((((8890458792185846579086418069 * 10 ^ 70 +
        3913206810433571881740961657108288681295567665658569441302789338670000) * 10 ^ 70 +
        0102029708861417910911637527861432778763220348525052344132414386292689) * 10 ^ 70 +
        6256503830038625213234751228772932674736910595417826183221697567431871) * 10 ^ 70 +
        5335149418728920587234740841129359762774381197345639911416972617949761) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (248 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_248_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (249 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (249 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_249 :
    recurrence4Scalar1First.coeff 249 =
      -(((((9199068653613667269344445321 * 10 ^ 70 +
        3572826655456329095975784893538487962295077951749322382546621386383165) * 10 ^ 70 +
        7523631256558062448779370419209231238024159187050967980520739523850984) * 10 ^ 70 +
        8099589367911998570163382981797459879480546942174121351475426298907729) * 10 ^ 70 +
        6248823646165655520702552934018935531169686433499085041455810564790997) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (249 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_249_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (250 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (250 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_250 :
    recurrence4Scalar1First.coeff 250 =
      (((((9358945625130167356467591005 * 10 ^ 70 +
        9793341473997767117473888638625093841140461606206957322809561774411079) * 10 ^ 70 +
        3564036007162793316858711234599222865035730080625980083303712142266334) * 10 ^ 70 +
        8270910212088862955408117022558098383484469718925090252204780864262115) * 10 ^ 70 +
        2202780388452134049680535753102566557673526798861417010775922313560925) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (250 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_250_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (251 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_251_suffix_zero :
    (∑ x ∈ Finset.range 75,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (251 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_251 :
    recurrence4Scalar1First.coeff 251 =
      -(((((9357110514433624707422587213 * 10 ^ 70 +
        9420132711999283005706538629586794333690492733951986909892902388593612) * 10 ^ 70 +
        3062496235725942974888064391577302663962172493375427268061237920957244) * 10 ^ 70 +
        7816572834186085343267221464583549882774704118876707415992556404024068) * 10 ^ 70 +
        4955261205914857802767803263881538794339298671003828054598330874299875) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 252,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (251 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_251_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_251_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (252 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_252_suffix_zero :
    (∑ x ∈ Finset.range 76,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (252 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_252 :
    recurrence4Scalar1First.coeff 252 =
      (((((9187650485676071438403236429 * 10 ^ 70 +
        6986319819658526238198433990652492217856160552936929587365968915018636) * 10 ^ 70 +
        6242221194585283412287160152323105646324213101025369387705126163564879) * 10 ^ 70 +
        5830246471676424073624719049532071490440963819227884187861939061777042) * 10 ^ 70 +
        2447404313208503810244538375948109951718956502205204141714651444190813) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 253,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (252 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_252_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_252_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (253 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_253_suffix_zero :
    (∑ x ∈ Finset.range 77,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (253 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_253 :
    recurrence4Scalar1First.coeff 253 =
      -(((((8852422809543305695221086617 * 10 ^ 70 +
        1912120193886854329827829027661180475794225808504214323126584472000001) * 10 ^ 70 +
        0138736057945957402212301931159469521832618491422091160751973096545920) * 10 ^ 70 +
        2243297348735784284957316043234507547472709426646663650317182011256293) * 10 ^ 70 +
        8223627557024815588288695992703390079014932797281736294170264626713506) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 254,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (253 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_253_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_253_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (254 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_254_suffix_zero :
    (∑ x ∈ Finset.range 78,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (254 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_254 :
    recurrence4Scalar1First.coeff 254 =
      (((((8361206436111990476365752571 * 10 ^ 70 +
        3416826320592960235733097552997357230651119689017008836538599144695590) * 10 ^ 70 +
        2460752524766288178277074097232376566298190294887528653127688083824904) * 10 ^ 70 +
        2464774642519370268809875119041405812693593321220139460482582508737915) * 10 ^ 70 +
        8720711967931244862039738846696012937608850771905471693311749914770605) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 255,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (254 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_254_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_254_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (255 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_255_suffix_zero :
    (∑ x ∈ Finset.range 79,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (255 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_255 :
    recurrence4Scalar1First.coeff 255 =
      -(((((7731266348164432733192318460 * 10 ^ 70 +
        8417019685829994244459381601954821660360812821499482358139199055060268) * 10 ^ 70 +
        5133948425307359657796821952147803520080456203125218717372889686340700) * 10 ^ 70 +
        4132384496097763158946524054648890435172569365916254733433162792066255) * 10 ^ 70 +
        9011464160405532245878248932204019383552125331761514181553418080696505) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 256,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (255 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_255_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_255_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (256 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_256_suffix_zero :
    (∑ x ∈ Finset.range 80,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (256 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_256 :
    recurrence4Scalar1First.coeff 256 =
      (((((6986353755536327965812155346 * 10 ^ 70 +
        2100641106439983343793859856264013741776112470992491039522924367661246) * 10 ^ 70 +
        8557413534019030170526942129297938395223852894301970798789137268814119) * 10 ^ 70 +
        5857374091242683323648767104007136029083252166540026796003179026435655) * 10 ^ 70 +
        0262790813930298993947681720880585040223762824365479600309096967823167) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 257,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (256 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_256_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_256_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (257 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_257_suffix_zero :
    (∑ x ∈ Finset.range 81,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (257 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_257 :
    recurrence4Scalar1First.coeff 257 =
      -(((((6155222323654323006031306434 * 10 ^ 70 +
        1632225317586428636212855199802853966937611752266333465407493669968061) * 10 ^ 70 +
        0726213619949978036368352070312614641847263888770958851474477316151828) * 10 ^ 70 +
        1357670798721230569984419080409567117724771515795260389392995171374368) * 10 ^ 70 +
        2045488974266302264172907565576984920578476929222368559606724125797169) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 258,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (257 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_257_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_257_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (258 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_258_suffix_zero :
    (∑ x ∈ Finset.range 82,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (258 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_258 :
    recurrence4Scalar1First.coeff 258 =
      (((((5269789573771078762391109483 * 10 ^ 70 +
        2994839037939907954583743301684149823527596824035635636613770295600105) * 10 ^ 70 +
        5551501499347350671562282572690892618321084160622889152467351423750746) * 10 ^ 70 +
        6646705157970292839782912009416905243581887900613612492722047104732776) * 10 ^ 70 +
        1030923850675155389782113473706549145778605231145195339930661363672124) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 259,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (258 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_258_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_258_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (259 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_259_suffix_zero :
    (∑ x ∈ Finset.range 83,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (259 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_259 :
    recurrence4Scalar1First.coeff 259 =
      -(((((4363107143174338829174718467 * 10 ^ 70 +
        9101023741562363719748966603862007707488223415361895093048381117189032) * 10 ^ 70 +
        4867464745919738490601746245853595421700126930522943673894354496725168) * 10 ^ 70 +
        3592315920030250289571333971594003085904790984548370542486691637711023) * 10 ^ 70 +
        2293310675786248395206544666222195290283100262983175542676889238054133) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 260,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (259 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_259_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_259_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (260 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_260_suffix_zero :
    (∑ x ∈ Finset.range 84,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (260 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_260 :
    recurrence4Scalar1First.coeff 260 =
      (((((3467319500298069214507749049 * 10 ^ 70 +
        5436948718859697579043095658130175875740607196585573120984518892562791) * 10 ^ 70 +
        5261295884209340804894550203315916235484533820218847313794563420325663) * 10 ^ 70 +
        9367341864643062273419801968011102823198078960636061967611836808876129) * 10 ^ 70 +
        8262744798940754636048602662047703817762212279811879409031015247992666) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 261,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (260 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_260_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_260_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (261 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_261_suffix_zero :
    (∑ x ∈ Finset.range 85,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (261 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_261 :
    recurrence4Scalar1First.coeff 261 =
      -(((((2611786305680769919204831531 * 10 ^ 70 +
        0415564696429846820960592433467340096996303003746356382511488799412961) * 10 ^ 70 +
        0603138891293873708093300692335941277636598041803907678839421229622359) * 10 ^ 70 +
        3662205265347154337870882087970160480839079769299211893181429287255572) * 10 ^ 70 +
        6505473895505702794901479843944582422857433811479583766456724751908418) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 262,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (261 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_261_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_261_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (262 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_262_suffix_zero :
    (∑ x ∈ Finset.range 86,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (262 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_262 :
    recurrence4Scalar1First.coeff 262 =
      (((((1821520020206115095666278504 * 10 ^ 70 +
        9257371000150656142513801539124519936069656163695733559029472901153533) * 10 ^ 70 +
        5932654234069542449121923647779921640584259632611017011447204139081753) * 10 ^ 70 +
        1669338488217136990942436260033483132373609539390079972803876772264021) * 10 ^ 70 +
        0325306879745232772730752701222403325032678354563406648052130416038857) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 263,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (262 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_262_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_262_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (263 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_263_suffix_zero :
    (∑ x ∈ Finset.range 87,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (263 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_263 :
    recurrence4Scalar1First.coeff 263 =
      -(((((1116051260313818281287010172 * 10 ^ 70 +
        1321666051470509084267207858166190536781665642777194287043602981711421) * 10 ^ 70 +
        2217134216464280323440763384300615112403981062902170128958420782015951) * 10 ^ 70 +
        9716533063439641420804877411233904228446836126837623035811524084473224) * 10 ^ 70 +
        4981284421228409312679477265867132337254061435852482560520679309351401) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 264,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (263 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_263_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_263_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (264 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_264_suffix_zero :
    (∑ x ∈ Finset.range 88,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (264 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_264 :
    recurrence4Scalar1First.coeff 264 =
      (((((508785367076976284112391351 * 10 ^ 70 +
        0522498017926497361194605872283607516225199879239242129909484759238739) * 10 ^ 70 +
        6435106659538113774574387001872376745240128466095939960642671924095838) * 10 ^ 70 +
        6946118142138282397107692320177799934446353085852591855021431562166211) * 10 ^ 70 +
        1810747237316173687920805250598397596591609492504913077197256182661742) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 265,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (264 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_264_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_264_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (265 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_265_suffix_zero :
    (∑ x ∈ Finset.range 89,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (265 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_265 :
    recurrence4Scalar1First.coeff 265 =
      -(((((6861269135811372516704554 * 10 ^ 70 +
        2460093851466351207458580491500277895840448491634897285352323906760838) * 10 ^ 70 +
        4649606840706665169120473829067079447109619535720677428379567687696964) * 10 ^ 70 +
        6359617639385872952653773074561155874385291946493711844184900596700721) * 10 ^ 70 +
        1366504930131594833107468651157427293965531584296643531363919996910615) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 266,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (265 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_265_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_265_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (266 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_266_suffix_zero :
    (∑ x ∈ Finset.range 90,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (266 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_266 :
    recurrence4Scalar1First.coeff 266 =
      -(((((388525464351660302903990261 * 10 ^ 70 +
        2497169189366654307163045637146984106963082230974403657237581350889925) * 10 ^ 70 +
        6978912488577647129706400972501973968494858388334363715882286382215592) * 10 ^ 70 +
        3459166125410813181163514907585886794663455134855854661060006405099115) * 10 ^ 70 +
        0623100963422829764039849328471122499980136914959267158164444351632347) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 267,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (266 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_266_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_266_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (267 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_267_suffix_zero :
    (∑ x ∈ Finset.range 91,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (267 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_267 :
    recurrence4Scalar1First.coeff 267 =
      (((((681413869247931001188188406 * 10 ^ 70 +
        3521385910883787892075827581120118775091513743017023263542622951562648) * 10 ^ 70 +
        4165565011345047116005874400877362841362895305873909492701285287079464) * 10 ^ 70 +
        3271432776383167448689186506400481407795217839452571716602304412303045) * 10 ^ 70 +
        2078481826141255216675496543498747511523898535254292372669525433343308) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 268,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (267 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_267_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_267_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (268 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_268_suffix_zero :
    (∑ x ∈ Finset.range 92,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (268 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_268 :
    recurrence4Scalar1First.coeff 268 =
      -(((((880089285052762548498327406 * 10 ^ 70 +
        5721323614091892001281992147643172727798819399168580278035501383667835) * 10 ^ 70 +
        9864342839500333502008373059929473127197585810957782332185484232731636) * 10 ^ 70 +
        4131034948696264485089696314625383710285125688253039702536528458915573) * 10 ^ 70 +
        5023673371600256305427454200324528627558703842998847533285724900751712) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 269,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (268 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_268_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_268_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (269 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 93,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (269 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_269 :
    recurrence4Scalar1First.coeff 269 =
      (((((995934756608911539483043049 * 10 ^ 70 +
        5858482938331764255387603132783522577290691853635115775080133591306409) * 10 ^ 70 +
        4410588499505340649680711990381677884187791615913541669975557497128028) * 10 ^ 70 +
        4982135973805402770407307598450494230182751857254587258125067996468433) * 10 ^ 70 +
        2363622813476907059342829188128117041471273713652806489395718930335724) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 270,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (269 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (270 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 94,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (270 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_270 :
    recurrence4Scalar1First.coeff 270 =
      -(((((1042240162360504421780972068 * 10 ^ 70 +
        4541451590952513904973965625953227833265341102924306926557253511006179) * 10 ^ 70 +
        5428095075878298335186081594262482109736990073933163457876071509104122) * 10 ^ 70 +
        5280834749791265423791943399056715885412375223803589345043504850097948) * 10 ^ 70 +
        6004196551389863749748965568752459468509308622412983085349813796586671) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 271,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (270 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (271 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 95,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (271 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_271 :
    recurrence4Scalar1First.coeff 271 =
      (((((1033073603604794416389596141 * 10 ^ 70 +
        0980825120380900098589374623552970925469247543765916820908070686166738) * 10 ^ 70 +
        6970081308065116996463295183807506644210319348467145558858039648011467) * 10 ^ 70 +
        5190535910153258783467314975440447449824997609343672137153010788851222) * 10 ^ 70 +
        5742396259333567899804107192635880247497194966111241775206959707962352) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 272,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (271 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (272 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 96,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (272 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_272 :
    recurrence4Scalar1First.coeff 272 =
      -(((((982297180969953776431624819 * 10 ^ 70 +
        5885092371724930893237041170947570976590878752869232406348405078681659) * 10 ^ 70 +
        4647142271396631719815127004340508814399689002379944105817344369952261) * 10 ^ 70 +
        1681933497381968897358241911269461347708663851175247329823074442977123) * 10 ^ 70 +
        7139897246099462076840986971919446280029226740937256977468066142981623) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 273,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (272 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (273 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 97,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (273 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_273 :
    recurrence4Scalar1First.coeff 273 =
      (((((902781936598908279310753157 * 10 ^ 70 +
        6366846590567034883836654640278319558980109553970442194495956245745604) * 10 ^ 70 +
        2994397692244323014858181795680249573462369497782819160987877808200677) * 10 ^ 70 +
        5076895580867355536843592883168752929036206092845797138093180550172379) * 10 ^ 70 +
        1833793841634354429726628186949349461320610938064605145889461028628726) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 274,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (273 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (274 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 98,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (274 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_274 :
    recurrence4Scalar1First.coeff 274 =
      -(((((805848422614463248574335973 * 10 ^ 70 +
        9098727309270454025739444570206183315035697704862074131766830031770000) * 10 ^ 70 +
        2698143570630561853552250559386046825486710032274261464534327048326468) * 10 ^ 70 +
        2336691997806779550584719776095026196518280732635360851834897195711686) * 10 ^ 70 +
        7530148133879736258015849543051585267407322941671197323245300150538104) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 275,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (274 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (275 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 99,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (275 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_275 :
    recurrence4Scalar1First.coeff 275 =
      (((((700933484978532282639874755 * 10 ^ 70 +
        4324013435352635519736678363069555052231715036081776231389266108456064) * 10 ^ 70 +
        7411032428321760154459165026123794015149919672547326819908966946520989) * 10 ^ 70 +
        0569700635280188990122329391579163975971443636360072558782423184391716) * 10 ^ 70 +
        1551259300607571968915062523643883473931324849018646406693447675737037) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 276,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (275 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence4Scalar1First_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4B3A4_coeff_high (276 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar1First_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 100,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4B3A4.coeff (276 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar1First_coeff_276 :
    recurrence4Scalar1First.coeff 276 =
      -(((((595462921268886877113191998 * 10 ^ 70 +
        3195134819992343225067954493462113747361521647251759284326898964541446) * 10 ^ 70 +
        0268843609785316846547161191956116629243311547033492668361821080335843) * 10 ^ 70 +
        8859259591636305190877063299969288930264370472369729295790506679226056) * 10 ^ 70 +
        5627360283352185768262474875111895249238426026077322549522834469416872) : ℚ) := by
  unfold recurrence4Scalar1First
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 277,
    remainder5Coefficient0.coeff x * recurrence4B3A4.coeff (276 - x)) = _
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
  rw [recurrence4Scalar1First_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar1First_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
