/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence5LookupScalar0LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 5 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fifth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence5LeadingSquare_coeff_0
  recurrence5LeadingSquare_coeff_1
  recurrence5LeadingSquare_coeff_2
  recurrence5LeadingSquare_coeff_3
  recurrence5LeadingSquare_coeff_4
  recurrence5LeadingSquare_coeff_5
  recurrence5LeadingSquare_coeff_6
  recurrence5LeadingSquare_coeff_7
  recurrence5LeadingSquare_coeff_8
  recurrence5LeadingSquare_coeff_9
  recurrence5LeadingSquare_coeff_10
  recurrence5LeadingSquare_coeff_11
  recurrence5LeadingSquare_coeff_12
  recurrence5LeadingSquare_coeff_13
  recurrence5LeadingSquare_coeff_14
  recurrence5LeadingSquare_coeff_15
  recurrence5LeadingSquare_coeff_16
  recurrence5LeadingSquare_coeff_17
  recurrence5LeadingSquare_coeff_18
  recurrence5LeadingSquare_coeff_19
  recurrence5LeadingSquare_coeff_20
  recurrence5LeadingSquare_coeff_21
  recurrence5LeadingSquare_coeff_22
  recurrence5LeadingSquare_coeff_23
  recurrence5LeadingSquare_coeff_24
  recurrence5LeadingSquare_coeff_25
  recurrence5LeadingSquare_coeff_26
  recurrence5LeadingSquare_coeff_27
  recurrence5LeadingSquare_coeff_28
  recurrence5LeadingSquare_coeff_29
  recurrence5LeadingSquare_coeff_30
  recurrence5LeadingSquare_coeff_31
  recurrence5LeadingSquare_coeff_32
  recurrence5LeadingSquare_coeff_33
  recurrence5LeadingSquare_coeff_34
  recurrence5LeadingSquare_coeff_35
  recurrence5LeadingSquare_coeff_36
  recurrence5LeadingSquare_coeff_37
  recurrence5LeadingSquare_coeff_38
  recurrence5LeadingSquare_coeff_39
  recurrence5LeadingSquare_coeff_40
  recurrence5LeadingSquare_coeff_41
  recurrence5LeadingSquare_coeff_42
  recurrence5LeadingSquare_coeff_43
  recurrence5LeadingSquare_coeff_44
  recurrence5LeadingSquare_coeff_45
  recurrence5LeadingSquare_coeff_46
  recurrence5LeadingSquare_coeff_47
  recurrence5LeadingSquare_coeff_48
  recurrence5LeadingSquare_coeff_49
  recurrence5LeadingSquare_coeff_50
  recurrence5LeadingSquare_coeff_51
  recurrence5LeadingSquare_coeff_52
  recurrence5LeadingSquare_coeff_53
  recurrence5LeadingSquare_coeff_54
  recurrence5LeadingSquare_coeff_55
  recurrence5LeadingSquare_coeff_56
  recurrence5LeadingSquare_coeff_57
  recurrence5LeadingSquare_coeff_58
  recurrence5LeadingSquare_coeff_59
  recurrence5LeadingSquare_coeff_60
  recurrence5LeadingSquare_coeff_61
  recurrence5LeadingSquare_coeff_62
  recurrence5LeadingSquare_coeff_63

attribute [local simp]
  recurrence5LeadingSquare_coeff_64
  recurrence5LeadingSquare_coeff_65
  recurrence5LeadingSquare_coeff_66
  recurrence5LeadingSquare_coeff_67
  recurrence5LeadingSquare_coeff_68
  recurrence5LeadingSquare_coeff_69
  recurrence5LeadingSquare_coeff_70
  recurrence5LeadingSquare_coeff_71
  recurrence5LeadingSquare_coeff_72
  recurrence5LeadingSquare_coeff_73
  recurrence5LeadingSquare_coeff_74
  recurrence5LeadingSquare_coeff_75
  recurrence5LeadingSquare_coeff_76
  recurrence5LeadingSquare_coeff_77
  recurrence5LeadingSquare_coeff_78
  recurrence5LeadingSquare_coeff_79
  recurrence5LeadingSquare_coeff_80
  recurrence5LeadingSquare_coeff_81
  recurrence5LeadingSquare_coeff_82
  recurrence5LeadingSquare_coeff_83
  recurrence5LeadingSquare_coeff_84
  recurrence5LeadingSquare_coeff_85
  recurrence5LeadingSquare_coeff_86
  recurrence5LeadingSquare_coeff_87
  recurrence5LeadingSquare_coeff_88
  recurrence5LeadingSquare_coeff_89
  recurrence5LeadingSquare_coeff_90
  recurrence5LeadingSquare_coeff_91
  recurrence5LeadingSquare_coeff_92
  recurrence5LeadingSquare_coeff_93
  recurrence5LeadingSquare_coeff_94
  recurrence5LeadingSquare_coeff_95
  recurrence5LeadingSquare_coeff_96
  recurrence5LeadingSquare_coeff_97
  recurrence5LeadingSquare_coeff_98
  recurrence5LeadingSquare_coeff_99
  recurrence5LeadingSquare_coeff_100
  recurrence5LeadingSquare_coeff_101
  recurrence5LeadingSquare_coeff_102
  recurrence5LeadingSquare_coeff_103
  recurrence5LeadingSquare_coeff_104
  recurrence5LeadingSquare_coeff_105
  recurrence5LeadingSquare_coeff_106
  recurrence5LeadingSquare_coeff_107
  recurrence5LeadingSquare_coeff_108
  recurrence5LeadingSquare_coeff_109
  recurrence5LeadingSquare_coeff_110
  recurrence5LeadingSquare_coeff_111
  recurrence5LeadingSquare_coeff_112
  recurrence5LeadingSquare_coeff_113
  recurrence5LeadingSquare_coeff_114
  recurrence5LeadingSquare_coeff_115
  recurrence5LeadingSquare_coeff_116
  recurrence5LeadingSquare_coeff_117
  recurrence5LeadingSquare_coeff_118
  recurrence5LeadingSquare_coeff_119
  recurrence5LeadingSquare_coeff_120
  recurrence5LeadingSquare_coeff_121
  recurrence5LeadingSquare_coeff_122
  recurrence5LeadingSquare_coeff_123
  recurrence5LeadingSquare_coeff_124
  recurrence5LeadingSquare_coeff_125
  recurrence5LeadingSquare_coeff_126
  recurrence5LeadingSquare_coeff_127

attribute [local simp]
  recurrence5LeadingSquare_coeff_128
  recurrence5LeadingSquare_coeff_129
  recurrence5LeadingSquare_coeff_130
  recurrence5LeadingSquare_coeff_131
  recurrence5LeadingSquare_coeff_132
  recurrence5LeadingSquare_coeff_133
  recurrence5LeadingSquare_coeff_134
  recurrence5LeadingSquare_coeff_135
  recurrence5LeadingSquare_coeff_136
  recurrence5LeadingSquare_coeff_137
  recurrence5LeadingSquare_coeff_138
  recurrence5LeadingSquare_coeff_139
  recurrence5LeadingSquare_coeff_140
  recurrence5LeadingSquare_coeff_141
  recurrence5LeadingSquare_coeff_142
  recurrence5LeadingSquare_coeff_143
  recurrence5LeadingSquare_coeff_144
  recurrence5LeadingSquare_coeff_145
  recurrence5LeadingSquare_coeff_146
  recurrence5LeadingSquare_coeff_147
  recurrence5LeadingSquare_coeff_148
  recurrence5LeadingSquare_coeff_149
  recurrence5LeadingSquare_coeff_150
  recurrence5LeadingSquare_coeff_151
  recurrence5LeadingSquare_coeff_152
  recurrence5LeadingSquare_coeff_153
  recurrence5LeadingSquare_coeff_154
  recurrence5LeadingSquare_coeff_155
  recurrence5LeadingSquare_coeff_156
  recurrence5LeadingSquare_coeff_157
  recurrence5LeadingSquare_coeff_158
  recurrence5LeadingSquare_coeff_159
  recurrence5LeadingSquare_coeff_160
  recurrence5LeadingSquare_coeff_161
  recurrence5LeadingSquare_coeff_162
  recurrence5LeadingSquare_coeff_163
  recurrence5LeadingSquare_coeff_164
  recurrence5LeadingSquare_coeff_165
  recurrence5LeadingSquare_coeff_166
  recurrence5LeadingSquare_coeff_167
  recurrence5LeadingSquare_coeff_168
  recurrence5LeadingSquare_coeff_169
  recurrence5LeadingSquare_coeff_170
  recurrence5LeadingSquare_coeff_171
  recurrence5LeadingSquare_coeff_172
  recurrence5LeadingSquare_coeff_173
  recurrence5LeadingSquare_coeff_174
  recurrence5LeadingSquare_coeff_175
  recurrence5LeadingSquare_coeff_176
  recurrence5LeadingSquare_coeff_177
  recurrence5LeadingSquare_coeff_178
  recurrence5LeadingSquare_coeff_179
  recurrence5LeadingSquare_coeff_180
  recurrence5LeadingSquare_coeff_181
  recurrence5LeadingSquare_coeff_182
  recurrence5LeadingSquare_coeff_183
  recurrence5LeadingSquare_coeff_184
  recurrence5LeadingSquare_coeff_185
  recurrence5LeadingSquare_coeff_186
  recurrence5LeadingSquare_coeff_187
  recurrence5LeadingSquare_coeff_188
  recurrence5LeadingSquare_coeff_189
  recurrence5LeadingSquare_coeff_190
  recurrence5LeadingSquare_coeff_191

attribute [local simp]
  recurrence5LeadingSquare_coeff_192
  recurrence5LeadingSquare_coeff_193
  recurrence5LeadingSquare_coeff_194
  recurrence5LeadingSquare_coeff_195
  recurrence5LeadingSquare_coeff_196
  recurrence5LeadingSquare_coeff_197
  recurrence5LeadingSquare_coeff_198
  recurrence5LeadingSquare_coeff_199
  recurrence5LeadingSquare_coeff_200
  recurrence5LeadingSquare_coeff_201
  recurrence5LeadingSquare_coeff_202
  recurrence5LeadingSquare_coeff_203
  recurrence5LeadingSquare_coeff_204
  recurrence5LeadingSquare_coeff_205
  recurrence5LeadingSquare_coeff_206
  recurrence5LeadingSquare_coeff_207
  recurrence5LeadingSquare_coeff_208
  recurrence5LeadingSquare_coeff_209
  recurrence5LeadingSquare_coeff_210
  recurrence5LeadingSquare_coeff_211
  recurrence5LeadingSquare_coeff_212
  recurrence5LeadingSquare_coeff_213
  recurrence5LeadingSquare_coeff_214
  recurrence5LeadingSquare_coeff_215
  recurrence5LeadingSquare_coeff_216
  recurrence5LeadingSquare_coeff_217
  recurrence5LeadingSquare_coeff_218
  recurrence5LeadingSquare_coeff_219
  recurrence5LeadingSquare_coeff_220
  recurrence5LeadingSquare_coeff_221
  recurrence5LeadingSquare_coeff_222
  recurrence5LeadingSquare_coeff_223
  recurrence5LeadingSquare_coeff_224
  recurrence5LeadingSquare_coeff_225
  recurrence5LeadingSquare_coeff_226
  recurrence5LeadingSquare_coeff_227
  recurrence5LeadingSquare_coeff_228
  recurrence5LeadingSquare_coeff_229
  recurrence5LeadingSquare_coeff_230
  recurrence5LeadingSquare_coeff_231
  recurrence5LeadingSquare_coeff_232
  recurrence5LeadingSquare_coeff_233
  recurrence5LeadingSquare_coeff_234
  recurrence5LeadingSquare_coeff_235
  recurrence5LeadingSquare_coeff_236
  recurrence5LeadingSquare_coeff_237
  recurrence5LeadingSquare_coeff_238
  recurrence5LeadingSquare_coeff_239
  recurrence5LeadingSquare_coeff_240
  recurrence5LeadingSquare_coeff_241
  recurrence5LeadingSquare_coeff_242
  recurrence5LeadingSquare_coeff_243
  recurrence5LeadingSquare_coeff_244
  recurrence5LeadingSquare_coeff_245
  recurrence5LeadingSquare_coeff_246
  recurrence5LeadingSquare_coeff_247
  recurrence5LeadingSquare_coeff_248
  recurrence5LeadingSquare_coeff_249
  recurrence5LeadingSquare_coeff_250
  recurrence5LeadingSquare_coeff_251
  recurrence5LeadingSquare_coeff_252
  recurrence5LeadingSquare_coeff_253
  recurrence5LeadingSquare_coeff_254
  recurrence5LeadingSquare_coeff_255

attribute [local simp]
  recurrence5LeadingSquare_coeff_256
  recurrence5LeadingSquare_coeff_257
  recurrence5LeadingSquare_coeff_258
  recurrence5LeadingSquare_coeff_259
  recurrence5LeadingSquare_coeff_260
  recurrence5LeadingSquare_coeff_261
  recurrence5LeadingSquare_coeff_262
  recurrence5LeadingSquare_coeff_263
  recurrence5LeadingSquare_coeff_264
  recurrence5LeadingSquare_coeff_265
  recurrence5LeadingSquare_coeff_266
  recurrence5LeadingSquare_coeff_267
  recurrence5LeadingSquare_coeff_268
  recurrence5LeadingSquare_coeff_269
  recurrence5LeadingSquare_coeff_270
  recurrence5LeadingSquare_coeff_271
  recurrence5LeadingSquare_coeff_272
  recurrence5LeadingSquare_coeff_273
  recurrence5LeadingSquare_coeff_274
  recurrence5LeadingSquare_coeff_275
  recurrence5LeadingSquare_coeff_276
  recurrence5LeadingSquare_coeff_277
  recurrence5LeadingSquare_coeff_278
  recurrence5LeadingSquare_coeff_279
  recurrence5LeadingSquare_coeff_280
  recurrence5LeadingSquare_coeff_281
  recurrence5LeadingSquare_coeff_282
  recurrence5LeadingSquare_coeff_283
  recurrence5LeadingSquare_coeff_284
  recurrence5LeadingSquare_coeff_285
  recurrence5LeadingSquare_coeff_286
  recurrence5LeadingSquare_coeff_287
  recurrence5LeadingSquare_coeff_288
  recurrence5LeadingSquare_coeff_289
  recurrence5LeadingSquare_coeff_290
  recurrence5A0_coeff_0
  recurrence5A0_coeff_1
  recurrence5A0_coeff_2
  recurrence5A0_coeff_3
  recurrence5A0_coeff_4
  recurrence5A0_coeff_5
  recurrence5A0_coeff_6
  recurrence5A0_coeff_7
  recurrence5A0_coeff_8
  recurrence5A0_coeff_9
  recurrence5A0_coeff_10
  recurrence5A0_coeff_11
  recurrence5A0_coeff_12
  recurrence5A0_coeff_13
  recurrence5A0_coeff_14
  recurrence5A0_coeff_15
  recurrence5A0_coeff_16
  recurrence5A0_coeff_17
  recurrence5A0_coeff_18
  recurrence5A0_coeff_19
  recurrence5A0_coeff_20
  recurrence5A0_coeff_21
  recurrence5A0_coeff_22
  recurrence5A0_coeff_23
  recurrence5A0_coeff_24
  recurrence5A0_coeff_25
  recurrence5A0_coeff_26
  recurrence5A0_coeff_27
  recurrence5A0_coeff_28

attribute [local simp]
  recurrence5A0_coeff_29
  recurrence5A0_coeff_30
  recurrence5A0_coeff_31
  recurrence5A0_coeff_32
  recurrence5A0_coeff_33
  recurrence5A0_coeff_34
  recurrence5A0_coeff_35
  recurrence5A0_coeff_36
  recurrence5A0_coeff_37
  recurrence5A0_coeff_38
  recurrence5A0_coeff_39
  recurrence5A0_coeff_40
  recurrence5A0_coeff_41
  recurrence5A0_coeff_42
  recurrence5A0_coeff_43
  recurrence5A0_coeff_44
  recurrence5A0_coeff_45
  recurrence5A0_coeff_46
  recurrence5A0_coeff_47
  recurrence5A0_coeff_48
  recurrence5A0_coeff_49
  recurrence5A0_coeff_50
  recurrence5A0_coeff_51
  recurrence5A0_coeff_52
  recurrence5A0_coeff_53
  recurrence5A0_coeff_54
  recurrence5A0_coeff_55
  recurrence5A0_coeff_56
  recurrence5A0_coeff_57
  recurrence5A0_coeff_58
  recurrence5A0_coeff_59
  recurrence5A0_coeff_60
  recurrence5A0_coeff_61
  recurrence5A0_coeff_62
  recurrence5A0_coeff_63
  recurrence5A0_coeff_64
  recurrence5A0_coeff_65
  recurrence5A0_coeff_66
  recurrence5A0_coeff_67
  recurrence5A0_coeff_68
  recurrence5A0_coeff_69
  recurrence5A0_coeff_70
  recurrence5A0_coeff_71
  recurrence5A0_coeff_72
  recurrence5A0_coeff_73
  recurrence5A0_coeff_74
  recurrence5A0_coeff_75
  recurrence5A0_coeff_76
  recurrence5A0_coeff_77
  recurrence5A0_coeff_78
  recurrence5A0_coeff_79
  recurrence5A0_coeff_80
  recurrence5A0_coeff_81
  recurrence5A0_coeff_82
  recurrence5A0_coeff_83
  recurrence5A0_coeff_84
  recurrence5A0_coeff_85
  recurrence5A0_coeff_86
  recurrence5A0_coeff_87
  recurrence5A0_coeff_88
  recurrence5A0_coeff_89
  recurrence5A0_coeff_90
  recurrence5A0_coeff_91
  recurrence5A0_coeff_92

attribute [local simp]
  recurrence5A0_coeff_93
  recurrence5A0_coeff_94
  recurrence5A0_coeff_95
  recurrence5A0_coeff_96
  recurrence5A0_coeff_97
  recurrence5A0_coeff_98
  recurrence5A0_coeff_99
  recurrence5A0_coeff_100
  recurrence5A0_coeff_101
  recurrence5A0_coeff_102
  recurrence5A0_coeff_103
  recurrence5A0_coeff_104
  recurrence5A0_coeff_105
  recurrence5A0_coeff_106
  recurrence5A0_coeff_107
  recurrence5A0_coeff_108
  recurrence5A0_coeff_109
  recurrence5A0_coeff_110
  recurrence5A0_coeff_111
  recurrence5A0_coeff_112
  recurrence5A0_coeff_113
  recurrence5A0_coeff_114
  recurrence5A0_coeff_115
  recurrence5A0_coeff_116
  recurrence5A0_coeff_117
  recurrence5A0_coeff_118
  recurrence5A0_coeff_119
  recurrence5A0_coeff_120
  recurrence5A0_coeff_121
  recurrence5A0_coeff_122
  recurrence5A0_coeff_123
  recurrence5A0_coeff_124
  recurrence5A0_coeff_125
  recurrence5A0_coeff_126
  recurrence5A0_coeff_127
  recurrence5A0_coeff_128
  recurrence5A0_coeff_129
  recurrence5A0_coeff_130
  recurrence5A0_coeff_131
  recurrence5A0_coeff_132
  recurrence5A0_coeff_133
  recurrence5A0_coeff_134
  recurrence5A0_coeff_135
  recurrence5A0_coeff_136
  recurrence5A0_coeff_137
  recurrence5A0_coeff_138
  recurrence5A0_coeff_139
  recurrence5A0_coeff_140
  recurrence5A0_coeff_141
  recurrence5A0_coeff_142
  recurrence5A0_coeff_143
  recurrence5A0_coeff_144
  recurrence5A0_coeff_145
  recurrence5A0_coeff_146
  recurrence5A0_coeff_147
  recurrence5A0_coeff_148
  recurrence5A0_coeff_149
  recurrence5A0_coeff_150
  recurrence5A0_coeff_151
  recurrence5A0_coeff_152
  recurrence5A0_coeff_153
  recurrence5A0_coeff_154
  recurrence5A0_coeff_155
  recurrence5A0_coeff_156

attribute [local simp]
  recurrence5A0_coeff_157
  recurrence5A0_coeff_158
  recurrence5A0_coeff_159
  recurrence5A0_coeff_160
  recurrence5A0_coeff_161
  recurrence5A0_coeff_162
  recurrence5A0_coeff_163
  recurrence5A0_coeff_164
  recurrence5A0_coeff_165
  recurrence5A0_coeff_166
  recurrence5A0_coeff_167
  recurrence5A0_coeff_168
  recurrence5A0_coeff_169
  recurrence5A0_coeff_170
  recurrence5A0_coeff_171
  recurrence5A0_coeff_172
  recurrence5A0_coeff_173
  recurrence5A0_coeff_174
  recurrence5A0_coeff_175
  recurrence5A0_coeff_176

private theorem recurrence5Scalar0Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (331 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_331 :
    recurrence5Scalar0Left.coeff 331 =
      (((((1950083349234973605235406178935135163725830049740434758 * 10 ^ 70 +
        4529475961993783113032950772823184975242334524468936439173799233387633) * 10 ^ 70 +
        1384327263038667435680819438809829464429064307311110100932829344569393) * 10 ^ 70 +
        4578140733798539447717912063586745374060732761164442059143687780232444) * 10 ^ 70 +
        7799167481855943572210442731872737300900726073791649412465669208651171) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 332 = 155 +
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
    rw [show 49 = 8 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (332 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_332 :
    recurrence5Scalar0Left.coeff 332 =
      -(((((916914037481422170235090235861683659323034383349959509 * 10 ^ 70 +
        9397186417506572625840915637490121114333234754339879906193331746529218) * 10 ^ 70 +
        2069731016416616833453269831325691075648773472676686482519679515141982) * 10 ^ 70 +
        7099632518191674720548377598829331165208624663127116995881695263318392) * 10 ^ 70 +
        1979835801152609856500859916076760906171015268387553269597170888105216) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 333 = 156 +
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
    rw [show 49 = 7 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (333 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_333 :
    recurrence5Scalar0Left.coeff 333 =
      (((((424958548136031180749402751661568260059158677989925738 * 10 ^ 70 +
        0683693225139648274375213121256517545669379881711457940182343950643517) * 10 ^ 70 +
        9230651061021016326065520453326720485524008743969361409025052762231690) * 10 ^ 70 +
        4506550192910770380860324799953536124641246028922116403606100933166166) * 10 ^ 70 +
        5719873247705944289704915346044506752127876686512653262816817364884882) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 334 = 157 +
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
    rw [show 49 = 6 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (334 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_334 :
    recurrence5Scalar0Left.coeff 334 =
      -(((((193436491809578144428751943630534060921806616484245911 * 10 ^ 70 +
        7104072397538608038499888555265128377264333076110590016139468525614492) * 10 ^ 70 +
        9837038044682317656453938186374911354781562090777579513396050420554652) * 10 ^ 70 +
        9523862055255476646987067980721005073164477273389030808998261446262291) * 10 ^ 70 +
        9000249623734147565282237679801494047108388080785367024813810702421581) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 335 = 158 +
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
    rw [show 49 = 5 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (335 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_335 :
    recurrence5Scalar0Left.coeff 335 =
      (((((86284149112451693187851671993243165138322797770314301 * 10 ^ 70 +
        4242298712291618592569553398566946069825419111920830911740234448523956) * 10 ^ 70 +
        6546768377352257160621846140541022835619859781602241269475674926857920) * 10 ^ 70 +
        2098343688030320978547831932798342365486599095754653036659123051336674) * 10 ^ 70 +
        8396222653702279387143424078227168344686687878086766473573649276373112) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 336 = 159 +
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
    rw [show 49 = 4 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (336 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_336 :
    recurrence5Scalar0Left.coeff 336 =
      -(((((37666644419826888921557858151316755980047080130224023 * 10 ^ 70 +
        1967193646388141531157021922545834365685403081262171846137785497804237) * 10 ^ 70 +
        7819932709066084214583136759790484023679200174605685536941374929031270) * 10 ^ 70 +
        3946198793867021392377229200134515544676732561819146603345138414523194) * 10 ^ 70 +
        8841351816557892076165257518004328826986091641051324782250425943805985) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 337 = 160 +
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
    rw [show 49 = 3 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (337 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_337 :
    recurrence5Scalar0Left.coeff 337 =
      (((((16080784886895706933952695845435546593529134683594136 * 10 ^ 70 +
        2056442287900716861531572490960021419855282211877730014739352219647219) * 10 ^ 70 +
        1022702523004434097053403514270586437151067444017177009715095414585707) * 10 ^ 70 +
        7888648155156223312435791500852906843243967126354953341537813120657628) * 10 ^ 70 +
        4769793225132958710867009040398689586848409990490845577487572893935378) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 338 = 161 +
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
    rw [show 49 = 2 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (338 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_338 :
    recurrence5Scalar0Left.coeff 338 =
      -(((((6711609028359905113959351836372222786082164532371756 * 10 ^ 70 +
        7855100678506628725395666829438049534436791370724572539804057918683425) * 10 ^ 70 +
        9615943807341192785107634520900717462430772568950188507240652700889505) * 10 ^ 70 +
        6724103497553292579457186765723651250419529412503212337950499460565249) * 10 ^ 70 +
        3725975391935935752600604557560220202005390075552345817541979305923960) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 339 = 162 +
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
    rw [show 49 = 1 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (339 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_339 :
    recurrence5Scalar0Left.coeff 339 =
      (((((2738048859253106189787070831689736525648085398516192 * 10 ^ 70 +
        7917535458788734302730985015325853848643869739487031078878534890458323) * 10 ^ 70 +
        0295064626344512052720572563979483425796035926399562558249148807489036) * 10 ^ 70 +
        0967015371970058874186034952029838842590855214252107949238020848284542) * 10 ^ 70 +
        4402003215609962482656393839841498594551707636754785063470537683649028) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 340 = 163 +
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
  rw [recurrence5Scalar0Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (340 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_340 :
    recurrence5Scalar0Left.coeff 340 =
      -(((((1091714116899343337922542061468702018456906339166359 * 10 ^ 70 +
        8417918966440797463739370263355479901189656028754398554925996886349803) * 10 ^ 70 +
        2988234803333149036863604432665166758071604390631954757816665011730699) * 10 ^ 70 +
        7296247684201606241399847362263288578793378332310752020933759620424108) * 10 ^ 70 +
        4358712214397997006621425250715825701716832202013954252069019213353966) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 341 = 164 +
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
    rw [show 81 = 31 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (341 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_341 :
    recurrence5Scalar0Left.coeff 341 =
      (((((425388435897654470777195228682946191040598513172545 * 10 ^ 70 +
        9178665163715469904772142083636993156268262198998456388024060727774309) * 10 ^ 70 +
        1984343052924658097841020814315795747325761244455453212901920761499185) * 10 ^ 70 +
        1677450555210569980689697105234340432764974304501912950837827374762178) * 10 ^ 70 +
        8597998117723361557089880694506250535873126912558475215086713917337136) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 342 = 165 +
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
    rw [show 81 = 30 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (342 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_342 :
    recurrence5Scalar0Left.coeff 342 =
      -(((((161957168141125779423597157919452534100611533928081 * 10 ^ 70 +
        2959217890660905925471949871060176790747293129939293604305188052772009) * 10 ^ 70 +
        0198720125939553337358109265375150016418198530901941906667982576003243) * 10 ^ 70 +
        6568830017135470735083858243763312554724264570214774599058775564990177) * 10 ^ 70 +
        7407788651797552755651690396653240394951039665163123835460452586408445) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 343 = 166 +
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
    rw [show 81 = 29 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (343 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_343 :
    recurrence5Scalar0Left.coeff 343 =
      (((((60232951965623436850002172050525418814435943108994 * 10 ^ 70 +
        0372604453980484999970908312955765050113743018520782372466327609087951) * 10 ^ 70 +
        3102935736018626298876138381508319497249648492934787216221759102434697) * 10 ^ 70 +
        5517223614298052665093666365248370748999439552390309922351886289720854) * 10 ^ 70 +
        5704347780381980829550404696129967975843481886166208555843304936464306) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 344 = 167 +
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
    rw [show 81 = 28 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (344 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_344 :
    recurrence5Scalar0Left.coeff 344 =
      -(((((21872773653825969353990552842041869818102505878691 * 10 ^ 70 +
        3540894706725533093851870786116623711967007957105065541778036473946281) * 10 ^ 70 +
        7581530554624905229415724493813093843626361108912827519315367970768353) * 10 ^ 70 +
        7163327215056190151990947780088106324905498391552176424656486898975285) * 10 ^ 70 +
        9334025512371420618380687607046594708833539939198386170438212582146006) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 345 = 168 +
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
    rw [show 81 = 27 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (345 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_345 :
    recurrence5Scalar0Left.coeff 345 =
      (((((7750669259986380030399133670226590817240360808811 * 10 ^ 70 +
        7836387444253291913347767569994983480435571012068171463184826877874816) * 10 ^ 70 +
        0985652629565057473762516932044390215986589942219455214511575975617756) * 10 ^ 70 +
        7315810156405011146285227991724736537179609023061566899279830416772719) * 10 ^ 70 +
        5046595779295865215751759022075544120510486422808311025493211910365864) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 346 = 169 +
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
    rw [show 81 = 26 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (346 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_346 :
    recurrence5Scalar0Left.coeff 346 =
      -(((((2677661336138677747910914193684987059123916670593 * 10 ^ 70 +
        5400312074654906558987448481296176537160717834005236743205562517587750) * 10 ^ 70 +
        5596580572310220930127114814764330144184933551928551264059094444330426) * 10 ^ 70 +
        9990840983427022520378010553954605138971805111370690105364752273201465) * 10 ^ 70 +
        0205507215371095054204414470528914838295518095333493478145473428742782) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 347 = 170 +
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
    rw [show 81 = 25 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (347 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_347 :
    recurrence5Scalar0Left.coeff 347 =
      (((((900765368112635491366457107184521028219155303891 * 10 ^ 70 +
        2543913862326727516821287191766921354429989118997626835433660112144772) * 10 ^ 70 +
        1367055125464674699188856818417712837731904247518950312406153721416080) * 10 ^ 70 +
        3564026460395408431431799477755204821993174198998714391788104437025940) * 10 ^ 70 +
        5931020976962079524025707542188352178809008630189034905185942438298148) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 348 = 171 +
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
    rw [show 81 = 24 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (348 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_348 :
    recurrence5Scalar0Left.coeff 348 =
      -(((((294536793670391276724313303490745395003012916531 * 10 ^ 70 +
        9141797216115657796352819870702794638193940257458109938848709436298211) * 10 ^ 70 +
        4745550967921920350299995228354179576582990594393867902457330957818184) * 10 ^ 70 +
        9705302075829753466970062844124396150526690660034004290384570547032715) * 10 ^ 70 +
        6523044166347992966515555172024820145412921145238570907003742861035409) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 349 = 172 +
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
    rw [show 81 = 23 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (349 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_349 :
    recurrence5Scalar0Left.coeff 349 =
      (((((93374105433637686768136637805834887273365547826 * 10 ^ 70 +
        9087224172351656344663100083132225234121674461830609935706841651675705) * 10 ^ 70 +
        3684688432273389471325437347238841263039227693504867356004590815778738) * 10 ^ 70 +
        3135385979826887906272415454029226063336510659541694945425688199873150) * 10 ^ 70 +
        7950541156648675983720940958155781762425381459363743992326445574761158) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 350 = 173 +
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
    rw [show 81 = 22 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (350 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_350 :
    recurrence5Scalar0Left.coeff 350 =
      -(((((28589062639742545506205525889545404851430383012 * 10 ^ 70 +
        9262534225354482539618279405643349981598305026377651455542340565982680) * 10 ^ 70 +
        1626317352691810424579933199718959470467111548076526433814142563528690) * 10 ^ 70 +
        7695610208058970950586698684917690220314055679326567099742688689088198) * 10 ^ 70 +
        6927177152075575783722993103872885164892884427512286928036583085071934) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 351 = 174 +
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
    rw [show 81 = 21 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (351 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_351 :
    recurrence5Scalar0Left.coeff 351 =
      (((((8402615965256606666553700842238360044312829138 * 10 ^ 70 +
        4532503827041421817097395950190298438990266824523133530824905756066075) * 10 ^ 70 +
        4944382036586391953241442734802047920244288088332165619877170615279036) * 10 ^ 70 +
        0620473221740441804908863440761958696797200395697758855639609858286809) * 10 ^ 70 +
        7339871453291351294850115649249971937901777209932462886316566543158716) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 352 = 175 +
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
    rw [show 81 = 20 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (352 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_352 :
    recurrence5Scalar0Left.coeff 352 =
      -(((((2346289498475325663262113612002199720964923689 * 10 ^ 70 +
        1955872878160488908648128400094913577163970643263920434142857676028361) * 10 ^ 70 +
        1048746397207146059211346004483752174843628829501292770824107788793112) * 10 ^ 70 +
        4133028436010222818857135609322971147256185344058054481479939552605664) * 10 ^ 70 +
        1255279508736509441247251543684015884362158184802137307832199443436060) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 353 = 176 +
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
    rw [show 81 = 19 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (353 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_353 :
    recurrence5Scalar0Left.coeff 353 =
      (((((610498595252305402878012962944759774107801034 * 10 ^ 70 +
        6982509467962306516060113401663447235348523392114917685498831575945948) * 10 ^ 70 +
        1283383702244332695336571324731637729117047878127432890178096232930825) * 10 ^ 70 +
        6807822066233168677909498601690927935747812735004234494765594921539394) * 10 ^ 70 +
        7492647767888701978756627257435445984136551434564167989455633748076412) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 354 = 177 +
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
    rw [show 81 = 18 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (354 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_354 :
    recurrence5Scalar0Left.coeff 354 =
      -(((((141866901424745152563001830062219744070245291 * 10 ^ 70 +
        1045596958607796207945658099822778062409336854199539794543751208929155) * 10 ^ 70 +
        7556061583334508046556402425454631012724867918062867920338868483976049) * 10 ^ 70 +
        4701784508695676315752985132593175661479148452786925500221001627975512) * 10 ^ 70 +
        0090978244843441706221631475362407319001353611717619122680829744052145) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 355 = 178 +
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
    rw [show 81 = 17 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence5Scalar0Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence5LeadingSquare.coeff x * remainder5Coefficient0.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5A0_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence5Scalar0Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence5LeadingSquare.coeff (291 + x) *
        remainder5Coefficient0.coeff (355 - (291 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence5LeadingSquare_coeff_high (291 + x) (by omega)]
  norm_num

theorem recurrence5Scalar0Left_coeff_355 :
    recurrence5Scalar0Left.coeff 355 =
      (((((26002417964176006053077378497663148472905506 * 10 ^ 70 +
        7111231570626789555998744853903574224214679551949908465401110766093619) * 10 ^ 70 +
        1293389833004107865324037256569949339878855581143970217394517218822979) * 10 ^ 70 +
        2746682030350558982299352755213191092186664364169785250417732471775782) * 10 ^ 70 +
        3374754186759274382636639353558302541320368235268846010313905769152100) : ℚ) := by
  unfold recurrence5Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Prod.fst, Prod.snd, Nat.succ_eq_add_one]
  rw [show 356 = 179 +
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
    rw [show 81 = 16 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence5Scalar0Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence5Scalar0Left_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
