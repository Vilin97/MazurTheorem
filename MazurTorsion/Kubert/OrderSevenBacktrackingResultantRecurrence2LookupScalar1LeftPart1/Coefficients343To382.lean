/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Left coefficient convolution

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
  recurrence2A1_coeff_0
  recurrence2A1_coeff_1
  recurrence2A1_coeff_2
  recurrence2A1_coeff_3
  recurrence2A1_coeff_4
  recurrence2A1_coeff_5
  recurrence2A1_coeff_6
  recurrence2A1_coeff_7
  recurrence2A1_coeff_8
  recurrence2A1_coeff_9
  recurrence2A1_coeff_10
  recurrence2A1_coeff_11
  recurrence2A1_coeff_12
  recurrence2A1_coeff_13
  recurrence2A1_coeff_14
  recurrence2A1_coeff_15
  recurrence2A1_coeff_16
  recurrence2A1_coeff_17
  recurrence2A1_coeff_18
  recurrence2A1_coeff_19
  recurrence2A1_coeff_20
  recurrence2A1_coeff_21
  recurrence2A1_coeff_22
  recurrence2A1_coeff_23
  recurrence2A1_coeff_24
  recurrence2A1_coeff_25
  recurrence2A1_coeff_26
  recurrence2A1_coeff_27
  recurrence2A1_coeff_28
  recurrence2A1_coeff_29
  recurrence2A1_coeff_30
  recurrence2A1_coeff_31
  recurrence2A1_coeff_32
  recurrence2A1_coeff_33
  recurrence2A1_coeff_34
  recurrence2A1_coeff_35
  recurrence2A1_coeff_36
  recurrence2A1_coeff_37
  recurrence2A1_coeff_38
  recurrence2A1_coeff_39
  recurrence2A1_coeff_40
  recurrence2A1_coeff_41
  recurrence2A1_coeff_42
  recurrence2A1_coeff_43
  recurrence2A1_coeff_44
  recurrence2A1_coeff_45
  recurrence2A1_coeff_46
  recurrence2A1_coeff_47
  recurrence2A1_coeff_48
  recurrence2A1_coeff_49
  recurrence2A1_coeff_50
  recurrence2A1_coeff_51
  recurrence2A1_coeff_52
  recurrence2A1_coeff_53
  recurrence2A1_coeff_54
  recurrence2A1_coeff_55
  recurrence2A1_coeff_56
  recurrence2A1_coeff_57
  recurrence2A1_coeff_58
  recurrence2A1_coeff_59
  recurrence2A1_coeff_60
  recurrence2A1_coeff_61
  recurrence2A1_coeff_62
  recurrence2A1_coeff_63
  recurrence2A1_coeff_64
  recurrence2A1_coeff_65
  recurrence2A1_coeff_66
  recurrence2A1_coeff_67
  recurrence2A1_coeff_68
  recurrence2A1_coeff_69
  recurrence2A1_coeff_70
  recurrence2A1_coeff_71
  recurrence2A1_coeff_72
  recurrence2A1_coeff_73
  recurrence2A1_coeff_74
  recurrence2A1_coeff_75
  recurrence2A1_coeff_76
  recurrence2A1_coeff_77
  recurrence2A1_coeff_78
  recurrence2A1_coeff_79
  recurrence2A1_coeff_80
  recurrence2A1_coeff_81
  recurrence2A1_coeff_82
  recurrence2A1_coeff_83
  recurrence2A1_coeff_84
  recurrence2A1_coeff_85
  recurrence2A1_coeff_86
  recurrence2A1_coeff_87
  recurrence2A1_coeff_88
  recurrence2A1_coeff_89
  recurrence2A1_coeff_90
  recurrence2A1_coeff_91
  recurrence2A1_coeff_92
  recurrence2A1_coeff_93
  recurrence2A1_coeff_94
  recurrence2A1_coeff_95
  recurrence2A1_coeff_96
  recurrence2A1_coeff_97
  recurrence2A1_coeff_98
  recurrence2A1_coeff_99
  recurrence2A1_coeff_100
  recurrence2A1_coeff_101
  recurrence2A1_coeff_102
  recurrence2A1_coeff_103
  recurrence2A1_coeff_104
  recurrence2A1_coeff_105
  recurrence2A1_coeff_106
  recurrence2A1_coeff_107
  recurrence2A1_coeff_108
  recurrence2A1_coeff_109
  recurrence2A1_coeff_110
  recurrence2A1_coeff_111
  recurrence2A1_coeff_112
  recurrence2A1_coeff_113
  recurrence2A1_coeff_114

private theorem recurrence2Scalar1Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (343 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_343 :
    recurrence2Scalar1Left.coeff 343 =
      (((106264274480 * 10 ^ 70 +
        6814571411831109442097630577851672612578973665324173530603072982484713) * 10 ^ 70 +
        7033000864214577513421234083421666422936253552315035285686725316243046) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 229 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 8 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (344 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_344 :
    recurrence2Scalar1Left.coeff 344 =
      -(((6773822134 * 10 ^ 70 +
        1208055943011889721969979349929217521630699335378258079091890354113073) * 10 ^ 70 +
        0564275985053379270083922548192863272618229472416000878827773788759590) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 230 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 7 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 231,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (345 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_345 :
    recurrence2Scalar1Left.coeff 345 =
      (((115204801 * 10 ^ 70 +
        0916750315939395323486123926520236980729331234154091860215923582694794) * 10 ^ 70 +
        8314343038446995699386337480718303786899549240086030800334209859008054) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 231 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 6 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_346_prefix_zero :
    (∑ x ∈ Finset.range 232,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (346 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (346 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_346_suffix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (346 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_346 :
    recurrence2Scalar1Left.coeff 346 =
      -(((185168 * 10 ^ 70 +
        7608737901709738504995726016344987255093541378586561074956636959409744) * 10 ^ 70 +
        0540831936404928181263316960635098852102467999617789081519417019205912) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 347 = 232 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 5 +
      78 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_346_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_346_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_347_prefix_zero :
    (∑ x ∈ Finset.range 233,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (347 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (347 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_347_suffix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (347 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_347 :
    recurrence2Scalar1Left.coeff 347 =
      -(((22716 * 10 ^ 70 +
        6520471649816162352469697509907477707299691745013470900811334146786833) * 10 ^ 70 +
        8774129284505129237569060117821983399553750740480041381584495865192609) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 348 = 233 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 4 +
      79 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_347_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_347_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_348_prefix_zero :
    (∑ x ∈ Finset.range 234,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (348 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (348 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_348_suffix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (348 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_348 :
    recurrence2Scalar1Left.coeff 348 =
      (((299 * 10 ^ 70 +
        8046358907122865094747147574037631311535667934190232773611408904717691) * 10 ^ 70 +
        6642446012654270393025534641472356023229090635782801743391414543124200) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 349 = 234 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 3 +
      80 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_348_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_348_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_349_prefix_zero :
    (∑ x ∈ Finset.range 235,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (349 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (349 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_349_suffix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (349 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_349 :
    recurrence2Scalar1Left.coeff 349 =
      ((1661529392045342920589503043931423136736819798137077556374492459807848 * 10 ^ 70 +
        2436113604810112537242192063866259839102645020323643872604848302930636) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 350 = 235 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 2 +
      81 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_349_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_349_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_350_prefix_zero :
    (∑ x ∈ Finset.range 236,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (350 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (350 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_350_suffix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (350 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_350 :
    recurrence2Scalar1Left.coeff 350 =
      -((306560041174230283385781006461806793795785011341724471632775664045835 * 10 ^ 70 +
        4941204032364684524998292441000016278058282581446871340606580401195456) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 351 = 236 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 1 +
      82 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_350_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_350_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_351_prefix_zero :
    (∑ x ∈ Finset.range 237,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (351 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (351 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_351_suffix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (351 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_351 :
    recurrence2Scalar1Left.coeff 351 =
      ((1483988204364485642267623385260842581020762459629617011966382624530 * 10 ^ 70 +
        1940631115509578575991325943531757562035288423436844609918195778105300) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 352 = 237 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_351_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_351_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_352_prefix_zero :
    (∑ x ∈ Finset.range 238,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (352 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (352 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_352_suffix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (352 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_352 :
    recurrence2Scalar1Left.coeff 352 =
      ((12484784953844247101068443148451583988335020946150549824604400518 * 10 ^ 70 +
        2272895139536038557851434021368729309922781731459253841768520976314171) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 353 = 238 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 31 +
      84 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_352_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_352_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_353_prefix_zero :
    (∑ x ∈ Finset.range 239,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (353 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (353 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_353_suffix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (353 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_353 :
    recurrence2Scalar1Left.coeff 353 =
      -((108444735861353135398573582447123053165023735362146350409398534 * 10 ^ 70 +
        8850901514931400834545368418637371638593228018801958827264676764594276) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 354 = 239 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 30 +
      85 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_353_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_353_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_354_prefix_zero :
    (∑ x ∈ Finset.range 240,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (354 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (354 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_354_suffix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (354 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_354 :
    recurrence2Scalar1Left.coeff 354 =
      -((198546443330854306920608291977535714257656879950753619706609 * 10 ^ 70 +
        3354785746679001002073996312016841069613250573316573803005617162703134) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 355 = 240 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 29 +
      86 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_354_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_354_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_355_prefix_zero :
    (∑ x ∈ Finset.range 241,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (355 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (355 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_355_suffix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (355 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_355 :
    recurrence2Scalar1Left.coeff 355 =
      ((3533092496281111610530569492243224340236122323345857175653 * 10 ^ 70 +
        0791133485888543526732643720633571724967333533696035943014340214871653) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 356 = 241 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 28 +
      87 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_355_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_355_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_356_prefix_zero :
    (∑ x ∈ Finset.range 242,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (356 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (356 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_356_suffix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (356 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_356 :
    recurrence2Scalar1Left.coeff 356 =
      -((1334581073622290943019353046975195873992757145368687145 * 10 ^ 70 +
        7621928043829566978061224151962610635138155030492842014438684488504129) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 357 = 242 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 27 +
      88 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_356_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_356_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_357_prefix_zero :
    (∑ x ∈ Finset.range 243,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (357 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (357 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_357_suffix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (357 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_357 :
    recurrence2Scalar1Left.coeff 357 =
      -((61178079857049879818727475619836345211050251990085862 * 10 ^ 70 +
        6109772442298649455107713720051587628588915948204253015515804094736307) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 358 = 243 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 26 +
      89 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_357_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_357_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_358_prefix_zero :
    (∑ x ∈ Finset.range 244,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (358 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (358 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_358_suffix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (358 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_358 :
    recurrence2Scalar1Left.coeff 358 =
      ((101863641604662185166095913114297738300073827341095 * 10 ^ 70 +
        1929327895797719681069331902021818649665395202840210057646083687966445) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 359 = 244 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 25 +
      90 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_358_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_358_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_359_prefix_zero :
    (∑ x ∈ Finset.range 245,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (359 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (359 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_359_suffix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (359 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_359 :
    recurrence2Scalar1Left.coeff 359 =
      ((543632657445540180848155799433408414098079799526 * 10 ^ 70 +
        6039679593768246779986596967288036606666542132122838975862455258964776) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 360 = 245 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 24 +
      91 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_359_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_359_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_360_prefix_zero :
    (∑ x ∈ Finset.range 246,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (360 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (360 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_360_suffix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (360 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_360 :
    recurrence2Scalar1Left.coeff 360 =
      -((1581492731051800337945189574321481388688414195 * 10 ^ 70 +
        9999135845263102378665107603779869105478027018729654117585646908579636) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 361 = 246 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 23 +
      92 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_360_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_360_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_361_prefix_zero :
    (∑ x ∈ Finset.range 247,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (361 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (361 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_361_suffix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (361 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_361 :
    recurrence2Scalar1Left.coeff 361 =
      -((1661591362279879300203042301222871157755761 * 10 ^ 70 +
        8047718337245325620075630431010492644803556948769179328176288863624101) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 362 = 247 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 22 +
      93 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_361_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_361_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_362_prefix_zero :
    (∑ x ∈ Finset.range 248,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (362 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (362 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_362_suffix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (362 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_362 :
    recurrence2Scalar1Left.coeff 362 =
      ((10451097340937136780988049522535958054789 * 10 ^ 70 +
        2784015276771513116836523708815495841682574840814643236979912745420793) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 363 = 248 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 21 +
      94 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_362_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_362_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_363_prefix_zero :
    (∑ x ∈ Finset.range 249,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (363 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (363 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_363_suffix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (363 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_363 :
    recurrence2Scalar1Left.coeff 363 =
      -((6899419781331775984097392496405021761 * 10 ^ 70 +
        4119269852094484666854185999283575629261995519270629855228936115830358) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 364 = 249 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 20 +
      95 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_363_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_363_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_364_prefix_zero :
    (∑ x ∈ Finset.range 250,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (364 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (364 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_364_suffix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (364 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_364 :
    recurrence2Scalar1Left.coeff 364 =
      -((22264049293086948498261270543406538 * 10 ^ 70 +
        9054051603512060521914276982680991988628670736888599082972204676021499) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 365 = 250 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 19 +
      96 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_364_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_364_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_365_prefix_zero :
    (∑ x ∈ Finset.range 251,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (365 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (365 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_365_suffix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (365 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_365 :
    recurrence2Scalar1Left.coeff 365 =
      ((43443752249319651849818465715779 * 10 ^ 70 +
        6528461119203300032668445556118774772252035936757187477515868892222783) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 366 = 251 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 18 +
      97 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_365_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_365_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_366_prefix_zero :
    (∑ x ∈ Finset.range 252,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (366 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (366 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_366_suffix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (366 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_366 :
    recurrence2Scalar1Left.coeff 366 =
      -((22044493277373077708533220279 * 10 ^ 70 +
        7094259472079768524471023760466546288148620670552616583573732002828730) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 367 = 252 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 17 +
      98 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_366_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_366_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_367_prefix_zero :
    (∑ x ∈ Finset.range 253,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (367 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (367 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_367_suffix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (367 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_367 :
    recurrence2Scalar1Left.coeff 367 =
      -((11417795327328533739765206 * 10 ^ 70 +
        7435624760855465633179476002734039508497043571585100709247785421106418) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 368 = 253 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 16 +
      99 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_367_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_367_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_368_prefix_zero :
    (∑ x ∈ Finset.range 254,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (368 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (368 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_368_suffix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (368 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_368 :
    recurrence2Scalar1Left.coeff 368 =
      ((17534494197285032405327 * 10 ^ 70 +
        5850637300370924194983582853678949354808141236547493925312256191556762) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 369 = 254 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 15 +
      100 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_368_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_368_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_369_prefix_zero :
    (∑ x ∈ Finset.range 255,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (369 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (369 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_369_suffix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (369 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_369 :
    recurrence2Scalar1Left.coeff 369 =
      -((7227779281161761332 * 10 ^ 70 +
        5416526989168185293702358306918043270733188202013245877059789911584265) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 370 = 255 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 14 +
      101 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_369_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_369_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_370_prefix_zero :
    (∑ x ∈ Finset.range 256,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (370 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (370 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_370_suffix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (370 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_370 :
    recurrence2Scalar1Left.coeff 370 =
      ((1042365782994375 * 10 ^ 70 +
        5013418936273119362540610719861773286020809191363839777044828746534485) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 371 = 256 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 13 +
      102 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_370_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_370_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_371_prefix_zero :
    (∑ x ∈ Finset.range 257,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (371 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (371 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_371_suffix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (371 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_371 :
    recurrence2Scalar1Left.coeff 371 =
      ((37286950366 * 10 ^ 70 +
        2916546670396859963575282653113955981342342874577625252099111045397863) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 372 = 257 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 12 +
      103 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_371_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_371_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_372_prefix_zero :
    (∑ x ∈ Finset.range 258,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (372 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (372 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_372_suffix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (372 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_372 :
    recurrence2Scalar1Left.coeff 372 =
      -((22598184 * 10 ^ 70 +
        0163097564421896482569356380841355470249147306567749162781343411235572) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 373 = 258 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 11 +
      104 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_372_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_372_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_373_prefix_zero :
    (∑ x ∈ Finset.range 259,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (373 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (373 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_373_suffix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (373 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_373 :
    recurrence2Scalar1Left.coeff 373 =
      ((1788 * 10 ^ 70 +
        0023912892842298209354797097907871075162094997887473734715513562294960) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 374 = 259 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 10 +
      105 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_373_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_373_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_374_prefix_zero :
    (∑ x ∈ Finset.range 260,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (374 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (374 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_374_suffix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (374 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_374 :
    recurrence2Scalar1Left.coeff 374 =
      (-478354278313389548554022920687404751858210225727591483780855293785114 : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 375 = 260 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 9 +
      106 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_374_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_374_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_375_prefix_zero :
    (∑ x ∈ Finset.range 261,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (375 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (375 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_375_suffix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (375 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_375 :
    recurrence2Scalar1Left.coeff 375 =
      (2347267816208257567220119095299943492493239857106206617712059345 : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 376 = 261 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 8 +
      107 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_375_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_375_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_376_prefix_zero :
    (∑ x ∈ Finset.range 262,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (376 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (376 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_376_suffix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (376 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_376 :
    recurrence2Scalar1Left.coeff 376 =
      (31585866679297875487463985494902096537277018173364795849734 : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 377 = 262 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 7 +
      108 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_376_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_376_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_377_prefix_zero :
    (∑ x ∈ Finset.range 263,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (377 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (377 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_377_suffix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (377 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_377 :
    recurrence2Scalar1Left.coeff 377 =
      (-267987244507918947146469427044684512830104417651449311 : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 378 = 263 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 6 +
      109 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_377_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_377_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_378_prefix_zero :
    (∑ x ∈ Finset.range 264,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (378 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (378 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_378_suffix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (378 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_378 :
    recurrence2Scalar1Left.coeff 378 =
      (355161228661028715299657031966939635130671351374 : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 379 = 264 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 5 +
      110 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_378_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_378_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_379_prefix_zero :
    (∑ x ∈ Finset.range 265,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (379 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (379 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_379_suffix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (379 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_379 :
    recurrence2Scalar1Left.coeff 379 =
      (-126509314574720340110135742133306327146064 : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 380 = 265 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 4 +
      111 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_379_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_379_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_380_prefix_zero :
    (∑ x ∈ Finset.range 266,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (380 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (380 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_380_suffix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (380 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_380 :
    recurrence2Scalar1Left.coeff 380 =
      (-2566123251051757354072909453836390 : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 381 = 266 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 3 +
      112 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_380_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_380_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_381_prefix_zero :
    (∑ x ∈ Finset.range 267,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (381 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (381 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_381_suffix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (381 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_381 :
    recurrence2Scalar1Left.coeff 381 =
      (52493199771550849605501044 : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 382 = 267 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 2 +
      113 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_381_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_381_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_382_prefix_zero :
    (∑ x ∈ Finset.range 268,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (382 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (382 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_382_suffix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (382 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_382 :
    recurrence2Scalar1Left.coeff 382 =
      (-199284929430635089 : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 383 = 268 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 1 +
      114 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_382_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_382_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
