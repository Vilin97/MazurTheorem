/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA4
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar4LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar4Left coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence2LeadingSquare_coeff_0
  recurrence2LeadingSquare_coeff_1
  recurrence2LeadingSquare_coeff_2
  recurrence2LeadingSquare_coeff_3
  recurrence2LeadingSquare_coeff_4
  recurrence2LeadingSquare_coeff_5
  recurrence2LeadingSquare_coeff_6
  recurrence2LeadingSquare_coeff_7
  recurrence2LeadingSquare_coeff_8
  recurrence2LeadingSquare_coeff_9
  recurrence2LeadingSquare_coeff_10
  recurrence2LeadingSquare_coeff_11
  recurrence2LeadingSquare_coeff_12
  recurrence2LeadingSquare_coeff_13
  recurrence2LeadingSquare_coeff_14
  recurrence2LeadingSquare_coeff_15
  recurrence2LeadingSquare_coeff_16
  recurrence2LeadingSquare_coeff_17
  recurrence2LeadingSquare_coeff_18
  recurrence2LeadingSquare_coeff_19
  recurrence2LeadingSquare_coeff_20
  recurrence2LeadingSquare_coeff_21
  recurrence2LeadingSquare_coeff_22
  recurrence2LeadingSquare_coeff_23
  recurrence2LeadingSquare_coeff_24
  recurrence2LeadingSquare_coeff_25
  recurrence2LeadingSquare_coeff_26
  recurrence2LeadingSquare_coeff_27
  recurrence2LeadingSquare_coeff_28
  recurrence2LeadingSquare_coeff_29
  recurrence2LeadingSquare_coeff_30
  recurrence2LeadingSquare_coeff_31
  recurrence2LeadingSquare_coeff_32
  recurrence2LeadingSquare_coeff_33
  recurrence2LeadingSquare_coeff_34
  recurrence2LeadingSquare_coeff_35
  recurrence2LeadingSquare_coeff_36
  recurrence2LeadingSquare_coeff_37
  recurrence2LeadingSquare_coeff_38
  recurrence2LeadingSquare_coeff_39
  recurrence2LeadingSquare_coeff_40
  recurrence2LeadingSquare_coeff_41
  recurrence2LeadingSquare_coeff_42
  recurrence2LeadingSquare_coeff_43
  recurrence2LeadingSquare_coeff_44
  recurrence2LeadingSquare_coeff_45
  recurrence2LeadingSquare_coeff_46
  recurrence2LeadingSquare_coeff_47
  recurrence2LeadingSquare_coeff_48
  recurrence2LeadingSquare_coeff_49
  recurrence2LeadingSquare_coeff_50
  recurrence2LeadingSquare_coeff_51
  recurrence2LeadingSquare_coeff_52
  recurrence2LeadingSquare_coeff_53
  recurrence2LeadingSquare_coeff_54
  recurrence2LeadingSquare_coeff_55
  recurrence2LeadingSquare_coeff_56
  recurrence2LeadingSquare_coeff_57
  recurrence2LeadingSquare_coeff_58
  recurrence2LeadingSquare_coeff_59
  recurrence2LeadingSquare_coeff_60
  recurrence2LeadingSquare_coeff_61
  recurrence2LeadingSquare_coeff_62
  recurrence2LeadingSquare_coeff_63
  recurrence2LeadingSquare_coeff_64
  recurrence2LeadingSquare_coeff_65
  recurrence2LeadingSquare_coeff_66
  recurrence2LeadingSquare_coeff_67
  recurrence2LeadingSquare_coeff_68
  recurrence2LeadingSquare_coeff_69
  recurrence2LeadingSquare_coeff_70
  recurrence2LeadingSquare_coeff_71
  recurrence2LeadingSquare_coeff_72
  recurrence2LeadingSquare_coeff_73
  recurrence2LeadingSquare_coeff_74
  recurrence2LeadingSquare_coeff_75
  recurrence2LeadingSquare_coeff_76
  recurrence2LeadingSquare_coeff_77
  recurrence2LeadingSquare_coeff_78
  recurrence2LeadingSquare_coeff_79
  recurrence2LeadingSquare_coeff_80
  recurrence2LeadingSquare_coeff_81
  recurrence2LeadingSquare_coeff_82
  recurrence2LeadingSquare_coeff_83
  recurrence2LeadingSquare_coeff_84
  recurrence2LeadingSquare_coeff_85
  recurrence2LeadingSquare_coeff_86
  recurrence2LeadingSquare_coeff_87
  recurrence2LeadingSquare_coeff_88
  recurrence2LeadingSquare_coeff_89
  recurrence2LeadingSquare_coeff_90
  recurrence2LeadingSquare_coeff_91
  recurrence2LeadingSquare_coeff_92
  recurrence2LeadingSquare_coeff_93
  recurrence2LeadingSquare_coeff_94
  recurrence2LeadingSquare_coeff_95
  recurrence2LeadingSquare_coeff_96
  recurrence2LeadingSquare_coeff_97
  recurrence2LeadingSquare_coeff_98
  recurrence2LeadingSquare_coeff_99
  recurrence2LeadingSquare_coeff_100
  recurrence2LeadingSquare_coeff_101
  recurrence2LeadingSquare_coeff_102
  recurrence2LeadingSquare_coeff_103
  recurrence2LeadingSquare_coeff_104
  recurrence2LeadingSquare_coeff_105
  recurrence2LeadingSquare_coeff_106
  recurrence2LeadingSquare_coeff_107
  recurrence2LeadingSquare_coeff_108
  recurrence2LeadingSquare_coeff_109
  recurrence2LeadingSquare_coeff_110
  recurrence2LeadingSquare_coeff_111
  recurrence2LeadingSquare_coeff_112
  recurrence2LeadingSquare_coeff_113
  recurrence2LeadingSquare_coeff_114
  recurrence2LeadingSquare_coeff_115
  recurrence2LeadingSquare_coeff_116
  recurrence2LeadingSquare_coeff_117
  recurrence2LeadingSquare_coeff_118
  recurrence2LeadingSquare_coeff_119
  recurrence2LeadingSquare_coeff_120
  recurrence2LeadingSquare_coeff_121
  recurrence2LeadingSquare_coeff_122
  recurrence2LeadingSquare_coeff_123
  recurrence2LeadingSquare_coeff_124
  recurrence2LeadingSquare_coeff_125
  recurrence2LeadingSquare_coeff_126
  recurrence2LeadingSquare_coeff_127
  recurrence2LeadingSquare_coeff_128
  recurrence2LeadingSquare_coeff_129
  recurrence2LeadingSquare_coeff_130
  recurrence2LeadingSquare_coeff_131
  recurrence2LeadingSquare_coeff_132
  recurrence2LeadingSquare_coeff_133
  recurrence2LeadingSquare_coeff_134
  recurrence2LeadingSquare_coeff_135
  recurrence2LeadingSquare_coeff_136
  recurrence2LeadingSquare_coeff_137
  recurrence2LeadingSquare_coeff_138
  recurrence2LeadingSquare_coeff_139
  recurrence2LeadingSquare_coeff_140
  recurrence2LeadingSquare_coeff_141
  recurrence2LeadingSquare_coeff_142
  recurrence2LeadingSquare_coeff_143
  recurrence2LeadingSquare_coeff_144
  recurrence2LeadingSquare_coeff_145
  recurrence2LeadingSquare_coeff_146
  recurrence2LeadingSquare_coeff_147
  recurrence2LeadingSquare_coeff_148
  recurrence2LeadingSquare_coeff_149
  recurrence2LeadingSquare_coeff_150
  recurrence2LeadingSquare_coeff_151
  recurrence2LeadingSquare_coeff_152
  recurrence2LeadingSquare_coeff_153
  recurrence2LeadingSquare_coeff_154
  recurrence2LeadingSquare_coeff_155
  recurrence2LeadingSquare_coeff_156
  recurrence2LeadingSquare_coeff_157
  recurrence2LeadingSquare_coeff_158
  recurrence2LeadingSquare_coeff_159
  recurrence2LeadingSquare_coeff_160
  recurrence2LeadingSquare_coeff_161
  recurrence2LeadingSquare_coeff_162
  recurrence2LeadingSquare_coeff_163
  recurrence2LeadingSquare_coeff_164
  recurrence2LeadingSquare_coeff_165
  recurrence2LeadingSquare_coeff_166
  recurrence2LeadingSquare_coeff_167
  recurrence2LeadingSquare_coeff_168
  recurrence2LeadingSquare_coeff_169
  recurrence2LeadingSquare_coeff_170
  recurrence2LeadingSquare_coeff_171
  recurrence2LeadingSquare_coeff_172
  recurrence2LeadingSquare_coeff_173
  recurrence2LeadingSquare_coeff_174
  recurrence2LeadingSquare_coeff_175
  recurrence2LeadingSquare_coeff_176
  recurrence2LeadingSquare_coeff_177
  recurrence2LeadingSquare_coeff_178
  recurrence2LeadingSquare_coeff_179
  recurrence2LeadingSquare_coeff_180
  recurrence2LeadingSquare_coeff_181
  recurrence2LeadingSquare_coeff_182
  recurrence2LeadingSquare_coeff_183
  recurrence2LeadingSquare_coeff_184
  recurrence2LeadingSquare_coeff_185
  recurrence2LeadingSquare_coeff_186
  recurrence2LeadingSquare_coeff_187
  recurrence2LeadingSquare_coeff_188
  recurrence2LeadingSquare_coeff_189
  recurrence2LeadingSquare_coeff_190
  recurrence2LeadingSquare_coeff_191
  recurrence2LeadingSquare_coeff_192
  recurrence2LeadingSquare_coeff_193
  recurrence2LeadingSquare_coeff_194
  recurrence2LeadingSquare_coeff_195
  recurrence2LeadingSquare_coeff_196
  recurrence2LeadingSquare_coeff_197
  recurrence2LeadingSquare_coeff_198
  recurrence2LeadingSquare_coeff_199
  recurrence2LeadingSquare_coeff_200
  recurrence2LeadingSquare_coeff_201
  recurrence2LeadingSquare_coeff_202
  recurrence2LeadingSquare_coeff_203
  recurrence2LeadingSquare_coeff_204
  recurrence2LeadingSquare_coeff_205
  recurrence2LeadingSquare_coeff_206
  recurrence2LeadingSquare_coeff_207
  recurrence2LeadingSquare_coeff_208
  recurrence2LeadingSquare_coeff_209
  recurrence2LeadingSquare_coeff_210
  recurrence2LeadingSquare_coeff_211
  recurrence2LeadingSquare_coeff_212
  recurrence2LeadingSquare_coeff_213
  recurrence2LeadingSquare_coeff_214
  recurrence2LeadingSquare_coeff_215
  recurrence2LeadingSquare_coeff_216
  recurrence2LeadingSquare_coeff_217
  recurrence2LeadingSquare_coeff_218
  recurrence2LeadingSquare_coeff_219
  recurrence2LeadingSquare_coeff_220
  recurrence2LeadingSquare_coeff_221
  recurrence2LeadingSquare_coeff_222
  recurrence2LeadingSquare_coeff_223
  recurrence2LeadingSquare_coeff_224
  recurrence2LeadingSquare_coeff_225
  recurrence2LeadingSquare_coeff_226
  recurrence2LeadingSquare_coeff_227
  recurrence2LeadingSquare_coeff_228
  recurrence2LeadingSquare_coeff_229
  recurrence2LeadingSquare_coeff_230
  recurrence2LeadingSquare_coeff_231
  recurrence2LeadingSquare_coeff_232
  recurrence2LeadingSquare_coeff_233
  recurrence2LeadingSquare_coeff_234
  recurrence2LeadingSquare_coeff_235
  recurrence2LeadingSquare_coeff_236
  recurrence2LeadingSquare_coeff_237
  recurrence2LeadingSquare_coeff_238
  recurrence2LeadingSquare_coeff_239
  recurrence2LeadingSquare_coeff_240
  recurrence2LeadingSquare_coeff_241
  recurrence2LeadingSquare_coeff_242
  recurrence2LeadingSquare_coeff_243
  recurrence2LeadingSquare_coeff_244
  recurrence2LeadingSquare_coeff_245
  recurrence2LeadingSquare_coeff_246
  recurrence2LeadingSquare_coeff_247
  recurrence2LeadingSquare_coeff_248
  recurrence2LeadingSquare_coeff_249
  recurrence2LeadingSquare_coeff_250
  recurrence2LeadingSquare_coeff_251
  recurrence2LeadingSquare_coeff_252
  recurrence2LeadingSquare_coeff_253
  recurrence2LeadingSquare_coeff_254
  recurrence2LeadingSquare_coeff_255
  recurrence2LeadingSquare_coeff_256
  recurrence2LeadingSquare_coeff_257
  recurrence2LeadingSquare_coeff_258
  recurrence2LeadingSquare_coeff_259
  recurrence2LeadingSquare_coeff_260
  recurrence2LeadingSquare_coeff_261
  recurrence2LeadingSquare_coeff_262
  recurrence2LeadingSquare_coeff_263
  recurrence2LeadingSquare_coeff_264
  recurrence2LeadingSquare_coeff_265
  recurrence2LeadingSquare_coeff_266
  recurrence2LeadingSquare_coeff_267
  recurrence2LeadingSquare_coeff_268
  recurrence2A4_coeff_0
  recurrence2A4_coeff_1
  recurrence2A4_coeff_2
  recurrence2A4_coeff_3
  recurrence2A4_coeff_4
  recurrence2A4_coeff_5
  recurrence2A4_coeff_6
  recurrence2A4_coeff_7
  recurrence2A4_coeff_8
  recurrence2A4_coeff_9
  recurrence2A4_coeff_10
  recurrence2A4_coeff_11
  recurrence2A4_coeff_12
  recurrence2A4_coeff_13
  recurrence2A4_coeff_14
  recurrence2A4_coeff_15
  recurrence2A4_coeff_16
  recurrence2A4_coeff_17
  recurrence2A4_coeff_18
  recurrence2A4_coeff_19
  recurrence2A4_coeff_20
  recurrence2A4_coeff_21
  recurrence2A4_coeff_22
  recurrence2A4_coeff_23
  recurrence2A4_coeff_24
  recurrence2A4_coeff_25
  recurrence2A4_coeff_26
  recurrence2A4_coeff_27
  recurrence2A4_coeff_28
  recurrence2A4_coeff_29
  recurrence2A4_coeff_30
  recurrence2A4_coeff_31
  recurrence2A4_coeff_32
  recurrence2A4_coeff_33
  recurrence2A4_coeff_34
  recurrence2A4_coeff_35
  recurrence2A4_coeff_36
  recurrence2A4_coeff_37
  recurrence2A4_coeff_38
  recurrence2A4_coeff_39
  recurrence2A4_coeff_40
  recurrence2A4_coeff_41
  recurrence2A4_coeff_42
  recurrence2A4_coeff_43
  recurrence2A4_coeff_44
  recurrence2A4_coeff_45
  recurrence2A4_coeff_46
  recurrence2A4_coeff_47
  recurrence2A4_coeff_48
  recurrence2A4_coeff_49
  recurrence2A4_coeff_50
  recurrence2A4_coeff_51
  recurrence2A4_coeff_52
  recurrence2A4_coeff_53
  recurrence2A4_coeff_54
  recurrence2A4_coeff_55
  recurrence2A4_coeff_56
  recurrence2A4_coeff_57
  recurrence2A4_coeff_58
  recurrence2A4_coeff_59
  recurrence2A4_coeff_60
  recurrence2A4_coeff_61
  recurrence2A4_coeff_62
  recurrence2A4_coeff_63
  recurrence2A4_coeff_64
  recurrence2A4_coeff_65
  recurrence2A4_coeff_66
  recurrence2A4_coeff_67
  recurrence2A4_coeff_68
  recurrence2A4_coeff_69
  recurrence2A4_coeff_70
  recurrence2A4_coeff_71
  recurrence2A4_coeff_72
  recurrence2A4_coeff_73
  recurrence2A4_coeff_74
  recurrence2A4_coeff_75
  recurrence2A4_coeff_76
  recurrence2A4_coeff_77
  recurrence2A4_coeff_78
  recurrence2A4_coeff_79
  recurrence2A4_coeff_80
  recurrence2A4_coeff_81
  recurrence2A4_coeff_82
  recurrence2A4_coeff_83
  recurrence2A4_coeff_84
  recurrence2A4_coeff_85
  recurrence2A4_coeff_86
  recurrence2A4_coeff_87
  recurrence2A4_coeff_88
  recurrence2A4_coeff_89
  recurrence2A4_coeff_90
  recurrence2A4_coeff_91
  recurrence2A4_coeff_92
  recurrence2A4_coeff_93
  recurrence2A4_coeff_94
  recurrence2A4_coeff_95
  recurrence2A4_coeff_96
  recurrence2A4_coeff_97
  recurrence2A4_coeff_98
  recurrence2A4_coeff_99
  recurrence2A4_coeff_100
  recurrence2A4_coeff_101
  recurrence2A4_coeff_102

private theorem recurrence2Scalar4Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_230 :
    recurrence2Scalar4Left.coeff 230 =
      -((((1 * 10 ^ 70 +
        5594347229877197257086507692968598506553776305862268785957140223454106) * 10 ^ 70 +
        7774523051578560480720397293980841510090216224589135833353273368221448) * 10 ^ 70 +
        1191964212727635727402651924819291704238257366185574712878594658564173) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 128 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_230_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_231 :
    recurrence2Scalar4Left.coeff 231 =
      ((((1 * 10 ^ 70 +
        8302176042778726102135251237721071428831193500843105726455934780495413) * 10 ^ 70 +
        0283311702366876947002190657255279339387315396681177347364763948276992) * 10 ^ 70 +
        2792216370971157580074302060730622163543118534971953028049457699212896) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 129 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_231_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (232 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_232 :
    recurrence2Scalar4Left.coeff 232 =
      -((((2 * 10 ^ 70 +
        0317211993591922712811417105274417477507127688164130436429282767663905) * 10 ^ 70 +
        7966448932372170901128686161379733966582583827415790629805689551558794) * 10 ^ 70 +
        7532642903542777722791045844361223363897427535333166644740318224600806) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 233 = 130 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_232_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_233 :
    recurrence2Scalar4Left.coeff 233 =
      ((((2 * 10 ^ 70 +
        1359579737504193383254207127070912939515019742495053731176064739234155) * 10 ^ 70 +
        1947055081973801633940222451658633470219446813422203458111636775398333) * 10 ^ 70 +
        1839997614403483590897022318114578172461153078512085555674522467870048) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 131 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_233_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_234 :
    recurrence2Scalar4Left.coeff 234 =
      -((((2 * 10 ^ 70 +
        1253848248699937782283514995909881626602540938585641467908051642513549) * 10 ^ 70 +
        6067424814617787722616475385697667997987284143112718044450017646569340) * 10 ^ 70 +
        8098733882409361504817907583883802466853089144029318256004484060872515) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 132 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_234_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_235 :
    recurrence2Scalar4Left.coeff 235 =
      ((((1 * 10 ^ 70 +
        9964473394137407189114743581387285965543491179815015605655722756190416) * 10 ^ 70 +
        8553408133225839148119488736113393459542046824225744058718090599483515) * 10 ^ 70 +
        2413766806388702061342952881625845897647570287185550504480466451031099) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 133 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_235_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_236 :
    recurrence2Scalar4Left.coeff 236 =
      -((((1 * 10 ^ 70 +
        7606279168654311582291828146538166663526087260105734799890956236820151) * 10 ^ 70 +
        1389381526420697009641571987596891629125604451171583566210152980423072) * 10 ^ 70 +
        4864328556878270074878863034678915160195736193055851746318326085389387) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 134 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_236_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_237 :
    recurrence2Scalar4Left.coeff 237 =
      ((((1 * 10 ^ 70 +
        4427071782126127381390054331182186952866976075789027456662982136670249) * 10 ^ 70 +
        4400093840050997038910212722249475464326138356934161189514974914728428) * 10 ^ 70 +
        7081325055635604730379553290745571628375090955709028342452671742648168) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 135 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_237_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_238 :
    recurrence2Scalar4Left.coeff 238 =
      -((((1 * 10 ^ 70 +
        0766122872247943855935909321277396441763348264610466859383676522497970) * 10 ^ 70 +
        2973827957373619251421056892951908291391615870812874382282873018765173) * 10 ^ 70 +
        1382895554771672026806086886287491012428231651885665521691685649246450) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 136 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_238_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_239 :
    recurrence2Scalar4Left.coeff 239 =
      (((6997864591022792473285803080822857310581521207474370185794292963761414 * 10 ^ 70 +
        2147031880240401209814997660820355330118879805203646253801623153920703) * 10 ^ 70 +
        9128080614282351547895352798709041719284578841317638517312554278128423) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 137 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_239_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_240 :
    recurrence2Scalar4Left.coeff 240 =
      -(((3473145572099871807963506170813923718257489591283779993487395355990816 * 10 ^ 70 +
        9940365887698508948446204295231510364342714593267990733514317259321083) * 10 ^ 70 +
        5955945581036766191612232066093123798277274572146984523525895680343386) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 138 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_240_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_241 :
    recurrence2Scalar4Left.coeff 241 =
      (((470091032737798577562599647908080215584498172841326735499818835754806 * 10 ^ 70 +
        3938971833757502143097342291101076713649679397061742414668656821888483) * 10 ^ 70 +
        8672228853964394348670467758431234022362576949564697707733928182425511) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 139 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_241_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_242 :
    recurrence2Scalar4Left.coeff 242 =
      (((1836681327906337359207043214695441573750617174961129555520097937847008 * 10 ^ 70 +
        8097862684290745543237902637436007318197739823344006290728924815884362) * 10 ^ 70 +
        2594403490749687800598211803372392588812281577236256506870367918226709) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 140 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_242_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_243 :
    recurrence2Scalar4Left.coeff 243 =
      -(((3384835004265971471028422877554994166094906465146696876345035734637060 * 10 ^ 70 +
        3636204738574551245982537663823533300035145328535899447280272195770361) * 10 ^ 70 +
        8004553790997595019212560898658987058211192327409468750022195842852118) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 141 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_243_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_244 :
    recurrence2Scalar4Left.coeff 244 =
      (((4212747760304200674175023028126776985469458276218615812579341160503897 * 10 ^ 70 +
        2445969431243879753495059405640031819937914478444974704228366944832965) * 10 ^ 70 +
        1915008748327976629823963461636098175577980501662383259111918082967975) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 142 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_244_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_245 :
    recurrence2Scalar4Left.coeff 245 =
      -(((4433388853574410845350961220429961642850760721525700370062376754830907 * 10 ^ 70 +
        1982543942809163634838311259258641836743972141841706536129368462385244) * 10 ^ 70 +
        8052192506054734880772226653439707742667399357276068672784107200785594) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 143 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_245_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_246 :
    recurrence2Scalar4Left.coeff 246 =
      (((4201455482941165693174749500311970302339401971279783053514781830274387 * 10 ^ 70 +
        1575607645987142109638099135520381322320915593187727167031671959887397) * 10 ^ 70 +
        7208740995142980621590212404526944440094014728948781667469245400662422) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 144 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_246_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_247 :
    recurrence2Scalar4Left.coeff 247 =
      -(((3681389671631285791330495803014978166800430145539137981978697186035135 * 10 ^ 70 +
        6702992098472508191202792157744528369738774264247474474334748392570313) * 10 ^ 70 +
        7322640487892079038883312819390746446858707576552517973831619660337647) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 145 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_247_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_248 :
    recurrence2Scalar4Left.coeff 248 =
      (((3021981713568628097072028233528259732562861700045693798267536749485669 * 10 ^ 70 +
        8042108323970126342496550406627927002048975825616682675606558771395422) * 10 ^ 70 +
        9694425272910172133742818275779644673060896360586497010216565224498398) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 146 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_248_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_249 :
    recurrence2Scalar4Left.coeff 249 =
      -(((2340496545462305801778116711310749227027802549608265992106732892319384 * 10 ^ 70 +
        9771486057009172379186140127398949956081617040736604384651405679579436) * 10 ^ 70 +
        8079238181852162983181137568476310513323851550197600358507184111402170) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 147 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_249_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_250 :
    recurrence2Scalar4Left.coeff 250 =
      (((1716531139504386515119241089084080763223034102171467965969438218428157 * 10 ^ 70 +
        2002065575593746251229179617148274270243780484045214321432760285655080) * 10 ^ 70 +
        0678693610431333252554302580109440002114139543147596344546683341097941) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 148 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_250_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_251 :
    recurrence2Scalar4Left.coeff 251 =
      -(((1193784013900056147498534449581351188730442479989296393912693831605701 * 10 ^ 70 +
        2271187823769313925559380429985928641806529429813836763608895087035894) * 10 ^ 70 +
        5280654693095710232242393414553166733436589255273859495241876695508044) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 149 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_251_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_252 :
    recurrence2Scalar4Left.coeff 252 =
      (((786888353788567171361233134505621162559500804116426819434767694727159 * 10 ^ 70 +
        3976553803184647580931399143627127424036405037180992961684199477725033) * 10 ^ 70 +
        9196485277100674907612403842767672678036099332391060769731959727982945) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 150 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_252_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_253 :
    recurrence2Scalar4Left.coeff 253 =
      -(((490377604371130330619709428265192466939333120753194786444632511319356 * 10 ^ 70 +
        6001291575451818531864878259245542265902310942255248298413420934659632) * 10 ^ 70 +
        9914640623962455172944890365531623801325725256961655077600258704290728) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 151 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_253_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_254 :
    recurrence2Scalar4Left.coeff 254 =
      (((287436104631812548001224475622828814922690176955164946004415172080685 * 10 ^ 70 +
        8148187093782819078459294929132360225753226519167217312351440608430315) * 10 ^ 70 +
        7668946324885521082685656558290072914243204375227191534152961824185312) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 152 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_254_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_255 :
    recurrence2Scalar4Left.coeff 255 =
      -(((156976193741597635403604673081333346694652842189901387991455958392555 * 10 ^ 70 +
        3852888478779783895078105555299753027717232993506708518072970450669752) * 10 ^ 70 +
        3369633935966979192346322235894290477200620764465724575585930039524673) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 153 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_255_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_256 :
    recurrence2Scalar4Left.coeff 256 =
      (((78461220457999471074700057565506844965226856741561590739349305933098 * 10 ^ 70 +
        6324299918661523238079365343681594573468356028942644208918655970026303) * 10 ^ 70 +
        6800581169962996594450109718213908635463439732201170347552737274348567) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 154 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_256_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_257 :
    recurrence2Scalar4Left.coeff 257 =
      -(((34560551354461620139617070470513414541473761101605074776547801963726 * 10 ^ 70 +
        8558454236114920000822238421573965710837176609277458187451773165019471) * 10 ^ 70 +
        8588475046879860109018384338429872547619661346184788455974984553358059) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 155 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_257_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_258 :
    recurrence2Scalar4Left.coeff 258 =
      (((12105346670961816037596344364282612681342402068220608705328435746358 * 10 ^ 70 +
        0086182416394763177290908983461276717470486503573401741216643053230797) * 10 ^ 70 +
        5256927006936063337108998680960290630815217670966751931289734183245711) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 156 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_258_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_259 :
    recurrence2Scalar4Left.coeff 259 =
      -(((1938816571088313532989750865063844766442621455564124551209139581605 * 10 ^ 70 +
        4611573085190686196989266427966610737263637331508900272454989978544789) * 10 ^ 70 +
        5411791609619726922174865795772546082479332379193896046085366940229361) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 157 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_259_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_260 :
    recurrence2Scalar4Left.coeff 260 =
      -(((1798873611116863965471899991791546395496383207911626543714353251345 * 10 ^ 70 +
        0956358209486618385386358001452358780854645671354094908760842884454152) * 10 ^ 70 +
        6459831284710126850468841192033574855758430811537182392463536080832943) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 158 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_260_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_261 :
    recurrence2Scalar4Left.coeff 261 =
      (((2553281565533535537780282300453986003651099107799557808162417077232 * 10 ^ 70 +
        2601427630504700734826598300921684668169625808168754131724143381763122) * 10 ^ 70 +
        3737188737615316246386166715524774754217421732335957801616247280110976) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 159 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_261_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_262 :
    recurrence2Scalar4Left.coeff 262 =
      -(((2167302664756539289950677612566626641814261584941662373721089375555 * 10 ^ 70 +
        1940937030071756964615286770446326277252182959383485228098994817584532) * 10 ^ 70 +
        7045174986213077441310850613387600341728428428068201826941550124360274) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 160 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_262_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_263 :
    recurrence2Scalar4Left.coeff 263 =
      (((1515344050296534391982452189460280461418983310003854441060899583746 * 10 ^ 70 +
        3084665062572725303100366347805604561413013782867575713436145195456551) * 10 ^ 70 +
        6491115371176800070437551908385364256185408635961648493821410255855888) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 161 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_263_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_264 :
    recurrence2Scalar4Left.coeff 264 =
      -(((942372362649464271823275130257863669258410852188050350816577316477 * 10 ^ 70 +
        4570112848300965055272414345131762890666373030170546561876795007073728) * 10 ^ 70 +
        0619709087493704370110094708024520074836400351471798288674691250969526) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 162 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_264_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_265 :
    recurrence2Scalar4Left.coeff 265 =
      (((537073102113157396014688895283306360411534323433850211679919062339 * 10 ^ 70 +
        0468861228009169370561530707983217018840179430349954912971950487513111) * 10 ^ 70 +
        4169818629864002282650144188025180158898173817565732054448073743353516) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 163 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_265_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_266 :
    recurrence2Scalar4Left.coeff 266 =
      -(((284424307330580038453964801348303707002994624033683040886819335503 * 10 ^ 70 +
        9868927326959048163302356316266773383288628861615735313315777832588603) * 10 ^ 70 +
        6341298950552061068037736784031094093149746885291973864102773449469381) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 164 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_266_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_267 :
    recurrence2Scalar4Left.coeff 267 =
      (((140879711565414060001612384706728835868241964233185545822927802832 * 10 ^ 70 +
        5774504450392870505358911664820139937653057642945634840033680099520200) * 10 ^ 70 +
        1471104635817953877892198621063690282166363860940342793969635569793346) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 165 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_267_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_268 :
    recurrence2Scalar4Left.coeff 268 =
      -(((65406352064701771735609339796078760690419149300310597634932134482 * 10 ^ 70 +
        5117989971389398795953032883275726161644530091039089231864412340325765) * 10 ^ 70 +
        4364062343318427316414864650280602201254424378408415655043766412653602) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 166 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 7 = 7 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_268_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
