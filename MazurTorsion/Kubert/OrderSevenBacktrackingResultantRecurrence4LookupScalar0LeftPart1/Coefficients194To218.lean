/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Left coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
