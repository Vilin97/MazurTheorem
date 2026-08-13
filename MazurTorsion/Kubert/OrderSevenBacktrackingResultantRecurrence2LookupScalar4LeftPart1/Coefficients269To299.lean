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

private theorem recurrence2Scalar4Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (269 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_269 :
    recurrence2Scalar4Left.coeff 269 =
      (((28427970017993771507080412894788068136120555081193291051548715681 * 10 ^ 70 +
        6011915415710140948170712271178475452516449963036285637551913175485444) * 10 ^ 70 +
        7091026198380642034338994237446765905719149304994840577505977930252393) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 167 +
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
    rw [show 7 = 6 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_269_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (270 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_270 :
    recurrence2Scalar4Left.coeff 270 =
      -(((11510293473120708703611579634731686058673394796206928559045602110 * 10 ^ 70 +
        7377526094437848321167958400489984192319493169374069761680068248023925) * 10 ^ 70 +
        1474563383068953637748543236887482213552415101640645296320578045469808) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 168 +
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
    rw [show 7 = 5 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_270_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (271 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_271 :
    recurrence2Scalar4Left.coeff 271 =
      (((4296614298140162404018048278698315561752261419226833937469332391 * 10 ^ 70 +
        4144832620549594422476946282955812889649571990306445971038847240705841) * 10 ^ 70 +
        2454817955891048794930339520057049514574111790022526708554563641353226) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 169 +
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
    rw [show 7 = 4 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (272 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_272 :
    recurrence2Scalar4Left.coeff 272 =
      -(((1448085344032067502770306113331825953981639131034672403396249708 * 10 ^ 70 +
        5373378360006952532589086441546942402915317379905268722408349609248225) * 10 ^ 70 +
        4265162534984675837972545344662646592023905595825332964368373194653546) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 170 +
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
    rw [show 7 = 3 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (273 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_273 :
    recurrence2Scalar4Left.coeff 273 =
      (((420450192132521630357486273720824931292589631884824166964412735 * 10 ^ 70 +
        1675470434678709221668124604812677776109385322946475331199390525215215) * 10 ^ 70 +
        8997888327656599569378058875078717104780234552324159967007613521541926) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 171 +
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
    rw [show 7 = 2 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (274 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_274 :
    recurrence2Scalar4Left.coeff 274 =
      -(((91300578828140533398622176780356450619325626113988039316254132 * 10 ^ 70 +
        7583388456479625759202387247480344336122448539062021741744871691976136) * 10 ^ 70 +
        8222555888114477222793769199811708811913067537195476615944893418656577) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 172 +
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
    rw [show 7 = 1 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (275 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_275 :
    recurrence2Scalar4Left.coeff 275 =
      (((4114714635489679352994626200800956295210012444669182375288588 * 10 ^ 70 +
        2517245726198283229186030472622313998876706494652831650077696723583425) * 10 ^ 70 +
        0317053807870997306181603231874432764134477770028488473609343545234937) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 173 +
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
  rw [recurrence2Scalar4Left_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (276 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_276 :
    recurrence2Scalar4Left.coeff 276 =
      (((10392680321115095816488363452174781262323775241857249414238572 * 10 ^ 70 +
        3782482394332909854142199466910884097663012039666231133660615037115943) * 10 ^ 70 +
        2454071175313344115912836910024230212205696681938475077631503062061958) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 174 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 31 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (277 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_277 :
    recurrence2Scalar4Left.coeff 277 =
      -(((8046710335714732988993378397088585326572757160810114334765657 * 10 ^ 70 +
        2510439117175715077798866303439446220871649144171704989503882497010745) * 10 ^ 70 +
        9538872543910860464391292178347355849806590006000297541878687740449485) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 175 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 30 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (278 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_278 :
    recurrence2Scalar4Left.coeff 278 =
      (((4253791137616590615290580362117089726991850676695893576479406 * 10 ^ 70 +
        9300809602469059980278479880259573204675712243412201412017782148669079) * 10 ^ 70 +
        2108623816352614744121712549104310745566799799954746369417639828181581) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 176 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 29 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (279 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_279 :
    recurrence2Scalar4Left.coeff 279 =
      -(((1885275634202824625890844985690583379681913611180454277853059 * 10 ^ 70 +
        3894769358330479619991340798886902435572608166552913560098096500884548) * 10 ^ 70 +
        2129087966181079488796385521676843858070980901332552324461852548264414) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 177 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 28 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (280 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_280 :
    recurrence2Scalar4Left.coeff 280 =
      (((742092265898185163415386351938209228944289361264412252842093 * 10 ^ 70 +
        2290253663150701409673707835855084426128969324412324820959557929003814) * 10 ^ 70 +
        8578933491800368818431939985269610787597903127299641398539985654112113) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 178 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 27 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (281 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_281 :
    recurrence2Scalar4Left.coeff 281 =
      -(((265306703771013852536250085324508450940963712857308533033846 * 10 ^ 70 +
        3919980169893187050004711205263812928344243756255806542691155107921419) * 10 ^ 70 +
        6290614945798025339439129351617554584057947883309646913978645857727446) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 179 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 26 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (282 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_282 :
    recurrence2Scalar4Left.coeff 282 =
      (((86881799891303435095512332241954701801343443439841159763642 * 10 ^ 70 +
        0428302597427483182366668463132025253334591032562260685617207464596553) * 10 ^ 70 +
        1545622973919440928439104210100397083797996524762090320738133875009340) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 180 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 25 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (283 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_283 :
    recurrence2Scalar4Left.coeff 283 =
      -(((26071384310513519505814049392739300317006817343891484031931 * 10 ^ 70 +
        5628491259954131570852102491797484318054528517260093476421240137945523) * 10 ^ 70 +
        5238861582135205041936214714959197947767134141474740896081698519008850) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 181 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 24 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (284 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_284 :
    recurrence2Scalar4Left.coeff 284 =
      (((7118207274410863827033690025056176970571665082082420458540 * 10 ^ 70 +
        4827420798902158824403197402147894441846491728333117195807312671609950) * 10 ^ 70 +
        6814126898771093205267224132587089421591014680817737885002414860282885) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 182 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 23 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (285 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_285 :
    recurrence2Scalar4Left.coeff 285 =
      -(((1736282065925091421718448179674578949236923858755212945775 * 10 ^ 70 +
        5494685501541256785329244810791143866991658734648419260062203396352235) * 10 ^ 70 +
        2981600231739178428359647960253929373875364462294896034708590293628624) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 183 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 22 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (286 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_286 :
    recurrence2Scalar4Left.coeff 286 =
      (((362389362052085944052438716606987229747704528572164555672 * 10 ^ 70 +
        2210506204547632418563160430596232248615975700015394756518523623416768) * 10 ^ 70 +
        5914223388130095739983987654417766435490924976376270978483187135333752) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 184 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 21 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (287 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_287 :
    recurrence2Scalar4Left.coeff 287 =
      -(((56937382280754893348948479744681794926664146287013709001 * 10 ^ 70 +
        5391646098736000640345546460808169247262034829225592177805898244892021) * 10 ^ 70 +
        2434939748835080229229551702266023413555761805702324982190252460719160) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 185 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 20 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (288 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_288 :
    recurrence2Scalar4Left.coeff 288 =
      (((2606981767087592999246844019782320777835855689410833586 * 10 ^ 70 +
        8843448551488518861036620593485221835715244058556400118661491878027555) * 10 ^ 70 +
        2909110041110080198811549227572758066700068319592389792869451330468994) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 186 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 19 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (289 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_289 :
    recurrence2Scalar4Left.coeff 289 =
      (((2668436677642448745970122373417747310491822395411568835 * 10 ^ 70 +
        7932056178384795780064913360988526196392348265466268722256604819110597) * 10 ^ 70 +
        4160804679625567056886439008432820509989636862402911920786474918144846) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 187 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 18 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (290 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_290 :
    recurrence2Scalar4Left.coeff 290 =
      -(((1468209251092698970368108145600861469426972637884189368 * 10 ^ 70 +
        0395546323149485402592590172349931028199991394029846335763120898266899) * 10 ^ 70 +
        7738132453768682318892393586472218039336691600920483968463884434380263) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 188 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 17 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (291 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_291 :
    recurrence2Scalar4Left.coeff 291 =
      (((525977744765869581421283024998222380556276698962660574 * 10 ^ 70 +
        5464938992207299973156172241759843669247325806446992257684786018285365) * 10 ^ 70 +
        3146788709104438918831320626277350557548841490247482501073815815317708) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 189 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 16 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (292 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_292 :
    recurrence2Scalar4Left.coeff 292 =
      -(((154292793797424938224845148192682551660013782471079350 * 10 ^ 70 +
        1652851545931657038218556625171174948670824180805089964535144571203863) * 10 ^ 70 +
        0767642255717460569434127471773318106943671966305413805952781033212506) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 190 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 15 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (293 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_293 :
    recurrence2Scalar4Left.coeff 293 =
      (((39309704832120650311090189159214876904407991299689230 * 10 ^ 70 +
        1221716171684843817269676272601996894922612878855222407402361104335164) * 10 ^ 70 +
        0551976984973656768653085813320400155121162055653140339617063149965128) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 191 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 14 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (294 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_294 :
    recurrence2Scalar4Left.coeff 294 =
      -(((8860445955804332551544309182193075844049375495891088 * 10 ^ 70 +
        3519969204792300586566522241354111170864331622675018233730712004173356) * 10 ^ 70 +
        8322275042097405050696151398427825830293891756614944869773148655730023) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 192 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 13 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (295 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_295 :
    recurrence2Scalar4Left.coeff 295 =
      (((1766233617528752172175754038472002302875010327630762 * 10 ^ 70 +
        4643595322035982917410001373635639930386025569216769887929768692022279) * 10 ^ 70 +
        5430763417868992203319405925204748235399807998416688656393030406018323) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 193 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 12 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (296 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_296 :
    recurrence2Scalar4Left.coeff 296 =
      -(((305702950738270039452472755989960054997906420432592 * 10 ^ 70 +
        4958426518972284467947335932644699132997795018335186374346644539106863) * 10 ^ 70 +
        1362864364036875599251907622188042801134909609046449572557212101921512) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 194 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 11 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (297 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_297 :
    recurrence2Scalar4Left.coeff 297 =
      (((43533056904275133006623156853806333104694217640612 * 10 ^ 70 +
        9704846700414654154743118953907065163408651669444785730412265451413521) * 10 ^ 70 +
        8137906491023853184119742929596666528605932153864320577733402334831824) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 195 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 10 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (298 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_298 :
    recurrence2Scalar4Left.coeff 298 =
      -(((4224019963070870916266269094855187712768480073246 * 10 ^ 70 +
        8055082257829541848739627011561564082084148521925646637566547845572229) * 10 ^ 70 +
        3342281952488215591456345826174412031801900607936388921945887519667515) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 196 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 9 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar4Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient4.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A4_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar4Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient4.coeff (299 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar4Left_coeff_299 :
    recurrence2Scalar4Left.coeff 299 =
      -(((62179020055548805274407778915589061093792655040 * 10 ^ 70 +
        6435377489150262929684673451723017437225645561701969570024440736309972) * 10 ^ 70 +
        8615205672098910433105637308463850670237644040829040961664285414226023) : ℚ) := by
  unfold recurrence2Scalar4Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 197 +
    103 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 32 +
      39 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 39 = 8 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar4Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar4Left_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
