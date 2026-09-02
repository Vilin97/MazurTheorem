/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA3
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar3LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar3Left coefficient convolution

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
  recurrence2A3_coeff_0
  recurrence2A3_coeff_1
  recurrence2A3_coeff_2
  recurrence2A3_coeff_3
  recurrence2A3_coeff_4
  recurrence2A3_coeff_5
  recurrence2A3_coeff_6
  recurrence2A3_coeff_7
  recurrence2A3_coeff_8
  recurrence2A3_coeff_9
  recurrence2A3_coeff_10
  recurrence2A3_coeff_11
  recurrence2A3_coeff_12
  recurrence2A3_coeff_13
  recurrence2A3_coeff_14
  recurrence2A3_coeff_15
  recurrence2A3_coeff_16
  recurrence2A3_coeff_17
  recurrence2A3_coeff_18
  recurrence2A3_coeff_19
  recurrence2A3_coeff_20
  recurrence2A3_coeff_21
  recurrence2A3_coeff_22
  recurrence2A3_coeff_23
  recurrence2A3_coeff_24
  recurrence2A3_coeff_25
  recurrence2A3_coeff_26
  recurrence2A3_coeff_27
  recurrence2A3_coeff_28
  recurrence2A3_coeff_29
  recurrence2A3_coeff_30
  recurrence2A3_coeff_31
  recurrence2A3_coeff_32
  recurrence2A3_coeff_33
  recurrence2A3_coeff_34
  recurrence2A3_coeff_35
  recurrence2A3_coeff_36
  recurrence2A3_coeff_37
  recurrence2A3_coeff_38
  recurrence2A3_coeff_39
  recurrence2A3_coeff_40
  recurrence2A3_coeff_41
  recurrence2A3_coeff_42
  recurrence2A3_coeff_43
  recurrence2A3_coeff_44
  recurrence2A3_coeff_45
  recurrence2A3_coeff_46
  recurrence2A3_coeff_47
  recurrence2A3_coeff_48
  recurrence2A3_coeff_49
  recurrence2A3_coeff_50
  recurrence2A3_coeff_51
  recurrence2A3_coeff_52
  recurrence2A3_coeff_53
  recurrence2A3_coeff_54
  recurrence2A3_coeff_55
  recurrence2A3_coeff_56
  recurrence2A3_coeff_57
  recurrence2A3_coeff_58
  recurrence2A3_coeff_59
  recurrence2A3_coeff_60
  recurrence2A3_coeff_61
  recurrence2A3_coeff_62
  recurrence2A3_coeff_63
  recurrence2A3_coeff_64
  recurrence2A3_coeff_65
  recurrence2A3_coeff_66
  recurrence2A3_coeff_67
  recurrence2A3_coeff_68
  recurrence2A3_coeff_69
  recurrence2A3_coeff_70
  recurrence2A3_coeff_71
  recurrence2A3_coeff_72
  recurrence2A3_coeff_73
  recurrence2A3_coeff_74
  recurrence2A3_coeff_75
  recurrence2A3_coeff_76
  recurrence2A3_coeff_77
  recurrence2A3_coeff_78
  recurrence2A3_coeff_79
  recurrence2A3_coeff_80
  recurrence2A3_coeff_81
  recurrence2A3_coeff_82
  recurrence2A3_coeff_83
  recurrence2A3_coeff_84
  recurrence2A3_coeff_85
  recurrence2A3_coeff_86
  recurrence2A3_coeff_87
  recurrence2A3_coeff_88
  recurrence2A3_coeff_89
  recurrence2A3_coeff_90
  recurrence2A3_coeff_91
  recurrence2A3_coeff_92
  recurrence2A3_coeff_93
  recurrence2A3_coeff_94
  recurrence2A3_coeff_95
  recurrence2A3_coeff_96
  recurrence2A3_coeff_97
  recurrence2A3_coeff_98
  recurrence2A3_coeff_99
  recurrence2A3_coeff_100
  recurrence2A3_coeff_101
  recurrence2A3_coeff_102
  recurrence2A3_coeff_103
  recurrence2A3_coeff_104
  recurrence2A3_coeff_105
  recurrence2A3_coeff_106

private theorem recurrence2Scalar3Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (271 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_271 :
    recurrence2Scalar3Left.coeff 271 =
      -(((434316069831086593216098100141482406719063516380174392265551877438 * 10 ^ 70 +
        8567000268776526763363848529917839056645586855884526731091778441689043) * 10 ^ 70 +
        4565231890202617250648216138681254154608443974583312244442798924008193) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 165 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 11 = 8 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_271_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (272 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_272 :
    recurrence2Scalar3Left.coeff 272 =
      (((144895382075903153247280153860803433708987632367002829943474574098 * 10 ^ 70 +
        2053412019253460676215801042710409202897192853323806042416937539534182) * 10 ^ 70 +
        4008316820125645075194731408782907935198225385797344953342869809515334) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 166 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 11 = 7 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (273 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_273 :
    recurrence2Scalar3Left.coeff 273 =
      -(((40369915356466298683709893028304729639928299332598716225666146434 * 10 ^ 70 +
        3053103883790582643243139641562881005776307838743508747423378736100183) * 10 ^ 70 +
        2810785387167289865446488927280579882230449416373792115276231251532777) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 167 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 11 = 6 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (274 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_274 :
    recurrence2Scalar3Left.coeff 274 =
      (((7371651751877989276675173635261135897417479133178265119751486295 * 10 ^ 70 +
        0120560800595718761038217791494855058275893123556668842592565243035595) * 10 ^ 70 +
        8022328014254603587123366479857243199678093463590740297325697554680042) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 168 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 11 = 5 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (275 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_275 :
    recurrence2Scalar3Left.coeff 275 =
      (((849246811898244258080914493936243068839255312366519810878500170 * 10 ^ 70 +
        1286477213066708179990269508406566651030424051297773510544584835363318) * 10 ^ 70 +
        3343861739981041713843715648497445341391663395785211383134605105613353) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 169 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 11 = 4 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (276 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_276 :
    recurrence2Scalar3Left.coeff 276 =
      -(((1783976599390030919080286878216595916531598092799215625580076262 * 10 ^ 70 +
        0612110386937745610338630705759458702925997050940776269979856036241235) * 10 ^ 70 +
        9421022493755161709957850342756160635702947544177633266131566012569145) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 170 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 11 = 3 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (277 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_277 :
    recurrence2Scalar3Left.coeff 277 =
      (((1189442142158938731499784629568347737550296114613875968701424625 * 10 ^ 70 +
        7984348155808856124633808370573042410724541674261529239710390572686249) * 10 ^ 70 +
        5966588018546307760326562852626065518517779366466153050933270344738198) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 171 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 11 = 2 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (278 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_278 :
    recurrence2Scalar3Left.coeff 278 =
      -(((603852247818257660857873324264719311084589280938070173966679875 * 10 ^ 70 +
        3161007195970213278964989740757728858694411329515413130457096659611962) * 10 ^ 70 +
        1293832768441161509013030262827539294773013457960967025681812137726429) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 172 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 11 = 1 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (279 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_279 :
    recurrence2Scalar3Left.coeff 279 =
      (((263745527854838823971464418939310248799332586398103005521575991 * 10 ^ 70 +
        2556670814906964440811648233325405047846180483754925629403706259020587) * 10 ^ 70 +
        5693355559319123023098170245668736233755608075774726689959633578248752) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 173 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 32 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (280 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_280 :
    recurrence2Scalar3Left.coeff 280 =
      -(((103128366643587837518272033000595646330285835096856647615054403 * 10 ^ 70 +
        6470281797179080481374846168459575674575269502782853994092568312678785) * 10 ^ 70 +
        9016408196833948803068243890068836468523342836720971961761414664476007) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 174 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 31 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (281 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_281 :
    recurrence2Scalar3Left.coeff 281 =
      (((36647092090124733202064388506832656000638118067520325964536380 * 10 ^ 70 +
        9544175266637682652437222063454144286324640661876317272033621825531188) * 10 ^ 70 +
        0713720817749329960448011295485522120588242705966290589463193562746884) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 175 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 30 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (282 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_282 :
    recurrence2Scalar3Left.coeff 282 =
      -(((11873205463013750423285514616691982898369280385946984692943227 * 10 ^ 70 +
        8241588785362172787134399175964015809012183677138833968874879162809391) * 10 ^ 70 +
        6758047280752069902174638685870823477804653917639340857005536672509936) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 176 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 29 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (283 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_283 :
    recurrence2Scalar3Left.coeff 283 =
      (((3486284559662488851052490656220839857792623510348756277130762 * 10 ^ 70 +
        4790520640906162283107261384088529655088416541212311444114464456987750) * 10 ^ 70 +
        0175783588906780209401495413267928182617680030552198217566189042894602) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 177 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 28 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (284 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_284 :
    recurrence2Scalar3Left.coeff 284 =
      -(((910785893493690236917916504026216710557234617567588700332459 * 10 ^ 70 +
        9026417581928162357463746149034341262110936396211100129416634336866916) * 10 ^ 70 +
        8802234848595928547116191895176916427243249239874261825812059881594783) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 178 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 27 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (285 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_285 :
    recurrence2Scalar3Left.coeff 285 =
      (((202279716822981723036107431506657243102215960811244445286695 * 10 ^ 70 +
        5607191889202733283174936805562234663654180269062157481467524342153616) * 10 ^ 70 +
        5471850845926596653049904917341264484495431667104807310969700501778841) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 179 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 26 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (286 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_286 :
    recurrence2Scalar3Left.coeff 286 =
      -(((33199562483496707529058535382820952440144262580437255163149 * 10 ^ 70 +
        8329421205311743021416361394673536969594144725382469935685423643401872) * 10 ^ 70 +
        5873467886425891251627758396096286485553171376887375282047879121113253) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 180 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 25 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (287 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_287 :
    recurrence2Scalar3Left.coeff 287 =
      (((1153546380953813016905086390015788760117072535095194832875 * 10 ^ 70 +
        4577944870034637161044659520097170079366437451842893915862857003330340) * 10 ^ 70 +
        1500703778537420219615251309643693840984484760219824124558346254850821) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 181 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 24 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (288 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_288 :
    recurrence2Scalar3Left.coeff 288 =
      (((2037191791666764524557826224393550972339258467353710386602 * 10 ^ 70 +
        1096500913987448302194533812998301885460954459820729304966738436462670) * 10 ^ 70 +
        9804859735361800658966297810260429641074995747433096690319224319124370) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 182 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 23 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (289 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_289 :
    recurrence2Scalar3Left.coeff 289 =
      -(((1139944849454389025610869780540873242551087576330215506831 * 10 ^ 70 +
        6456392274140915531953177802790844697767149385805988872543148891342377) * 10 ^ 70 +
        8794049604519850942104412801768428132562859156599084484168475130884678) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 183 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 22 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (290 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_290 :
    recurrence2Scalar3Left.coeff 290 =
      (((425671956373243048242988645623287629224591603408010799592 * 10 ^ 70 +
        2908124471102106863436747574877282073943557761864353197640497528976851) * 10 ^ 70 +
        1144827741011433669690256287654528129855526076968639379653862063526667) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 184 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 21 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (291 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_291 :
    recurrence2Scalar3Left.coeff 291 =
      -(((129745821592298905088680670409947193936524243212850523133 * 10 ^ 70 +
        2548981527809766043236639482096068078167107167725361360980825247689241) * 10 ^ 70 +
        6186146908000912027740861346845713286696085577072657070786381415802456) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 185 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 20 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (292 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_292 :
    recurrence2Scalar3Left.coeff 292 =
      (((33872963015563760586207504300870743870656869479596736673 * 10 ^ 70 +
        6204462404705550640664668622878826770436217147132889504582033910209198) * 10 ^ 70 +
        7296329217827020549704906690509115267554977349215352322206548347304392) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 186 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 19 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (293 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_293 :
    recurrence2Scalar3Left.coeff 293 =
      -(((7603089042989055738458025309144434501468696642094282378 * 10 ^ 70 +
        6749427979357848338458546100138585798281121999113497444054161163898331) * 10 ^ 70 +
        7674369824248847568667041387021728907303107572589164323147576733209391) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 187 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 18 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (294 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_294 :
    recurrence2Scalar3Left.coeff 294 =
      (((1419052720223751571944422779970857221116717647274002134 * 10 ^ 70 +
        5227329073628045752696506178526759739218637993869357994502122404960906) * 10 ^ 70 +
        6932057267701587581851475154183020907375114510519579650652908631716000) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 188 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 17 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (295 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_295 :
    recurrence2Scalar3Left.coeff 295 =
      -(((194003756542732719049738988906724825436138767935294431 * 10 ^ 70 +
        3826506934366555668380464996438483205333835560668243953276931929560794) * 10 ^ 70 +
        9599034754100388381513117760884878691975555090736517573840068191911537) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 189 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 16 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (296 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_296 :
    recurrence2Scalar3Left.coeff 296 =
      (((6880057698139600313940743723108941414520343344031620 * 10 ^ 70 +
        1240449705232015570366527914403337662342783183726866147468183265308211) * 10 ^ 70 +
        6022532868662731799005426043550624963109425824764645472168592865393954) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 190 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 15 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (297 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_297 :
    recurrence2Scalar3Left.coeff 297 =
      (((6968343319930727609644153030869861766676523044332966 * 10 ^ 70 +
        2250159409667240892342817752332525524016064999368277301766110009582322) * 10 ^ 70 +
        3152228260231353705510815322155990670202516872840254730206905268046412) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 191 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 14 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (298 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_298 :
    recurrence2Scalar3Left.coeff 298 =
      -(((3130518517728863549985892794080010383580671580744169 * 10 ^ 70 +
        1736830088714939532207038198681997698609202045401296191078042572486668) * 10 ^ 70 +
        5967357798926310432036364888516476059206650095447135721443407344272614) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 192 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 13 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (299 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_299 :
    recurrence2Scalar3Left.coeff 299 =
      (((905898633329504717402625642810049390201961155023202 * 10 ^ 70 +
        4550879286029373070153259481794034222649133207763808348831934179527296) * 10 ^ 70 +
        5383116513305398358748592134486148654066687332949853765173549523941957) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 193 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 12 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (300 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_300 :
    recurrence2Scalar3Left.coeff 300 =
      -(((209063476771636732478779418303799838820568916143858 * 10 ^ 70 +
        2618450284389013046462836037811222556122884553084584733188321899591296) * 10 ^ 70 +
        0307415701238141321333466906664082949156614833655688340713264792196433) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 194 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 11 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (301 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_301 :
    recurrence2Scalar3Left.coeff 301 =
      (((40215594208705658121168598327301841177826311830710 * 10 ^ 70 +
        6405273298286451831062528174481963979954535161775101956056009698583925) * 10 ^ 70 +
        5114382151083417756069182981072265663767680019258024392227779062570875) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 195 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 10 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (302 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_302 :
    recurrence2Scalar3Left.coeff 302 =
      -(((6371249380115264251495751393145544065269226544764 * 10 ^ 70 +
        5295576401610280460867788479696206812355644345498252545038946243736674) * 10 ^ 70 +
        3094854963038352795619165747704315573566668880068683612917061562098649) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 196 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 9 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
