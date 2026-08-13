/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar2Left coefficient convolution

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
  recurrence2A2_coeff_0
  recurrence2A2_coeff_1
  recurrence2A2_coeff_2
  recurrence2A2_coeff_3
  recurrence2A2_coeff_4
  recurrence2A2_coeff_5
  recurrence2A2_coeff_6
  recurrence2A2_coeff_7
  recurrence2A2_coeff_8
  recurrence2A2_coeff_9
  recurrence2A2_coeff_10
  recurrence2A2_coeff_11
  recurrence2A2_coeff_12
  recurrence2A2_coeff_13
  recurrence2A2_coeff_14
  recurrence2A2_coeff_15
  recurrence2A2_coeff_16
  recurrence2A2_coeff_17
  recurrence2A2_coeff_18
  recurrence2A2_coeff_19
  recurrence2A2_coeff_20
  recurrence2A2_coeff_21
  recurrence2A2_coeff_22
  recurrence2A2_coeff_23
  recurrence2A2_coeff_24
  recurrence2A2_coeff_25
  recurrence2A2_coeff_26
  recurrence2A2_coeff_27
  recurrence2A2_coeff_28
  recurrence2A2_coeff_29
  recurrence2A2_coeff_30
  recurrence2A2_coeff_31
  recurrence2A2_coeff_32
  recurrence2A2_coeff_33
  recurrence2A2_coeff_34
  recurrence2A2_coeff_35
  recurrence2A2_coeff_36
  recurrence2A2_coeff_37
  recurrence2A2_coeff_38
  recurrence2A2_coeff_39
  recurrence2A2_coeff_40
  recurrence2A2_coeff_41
  recurrence2A2_coeff_42
  recurrence2A2_coeff_43
  recurrence2A2_coeff_44
  recurrence2A2_coeff_45
  recurrence2A2_coeff_46
  recurrence2A2_coeff_47
  recurrence2A2_coeff_48
  recurrence2A2_coeff_49
  recurrence2A2_coeff_50
  recurrence2A2_coeff_51
  recurrence2A2_coeff_52
  recurrence2A2_coeff_53
  recurrence2A2_coeff_54
  recurrence2A2_coeff_55
  recurrence2A2_coeff_56
  recurrence2A2_coeff_57
  recurrence2A2_coeff_58
  recurrence2A2_coeff_59
  recurrence2A2_coeff_60
  recurrence2A2_coeff_61
  recurrence2A2_coeff_62
  recurrence2A2_coeff_63
  recurrence2A2_coeff_64
  recurrence2A2_coeff_65
  recurrence2A2_coeff_66
  recurrence2A2_coeff_67
  recurrence2A2_coeff_68
  recurrence2A2_coeff_69
  recurrence2A2_coeff_70
  recurrence2A2_coeff_71
  recurrence2A2_coeff_72
  recurrence2A2_coeff_73
  recurrence2A2_coeff_74
  recurrence2A2_coeff_75
  recurrence2A2_coeff_76
  recurrence2A2_coeff_77
  recurrence2A2_coeff_78
  recurrence2A2_coeff_79
  recurrence2A2_coeff_80
  recurrence2A2_coeff_81
  recurrence2A2_coeff_82
  recurrence2A2_coeff_83
  recurrence2A2_coeff_84
  recurrence2A2_coeff_85
  recurrence2A2_coeff_86
  recurrence2A2_coeff_87
  recurrence2A2_coeff_88
  recurrence2A2_coeff_89
  recurrence2A2_coeff_90
  recurrence2A2_coeff_91
  recurrence2A2_coeff_92
  recurrence2A2_coeff_93
  recurrence2A2_coeff_94
  recurrence2A2_coeff_95
  recurrence2A2_coeff_96
  recurrence2A2_coeff_97
  recurrence2A2_coeff_98
  recurrence2A2_coeff_99
  recurrence2A2_coeff_100
  recurrence2A2_coeff_101
  recurrence2A2_coeff_102
  recurrence2A2_coeff_103
  recurrence2A2_coeff_104
  recurrence2A2_coeff_105
  recurrence2A2_coeff_106
  recurrence2A2_coeff_107
  recurrence2A2_coeff_108
  recurrence2A2_coeff_109
  recurrence2A2_coeff_110

private theorem recurrence2Scalar2Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (272 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_272 :
    recurrence2Scalar2Left.coeff 272 =
      (((16150063731996286846521310063250967917278767763589251408286151564737 * 10 ^ 70 +
        5461112700138631852590631726554135837575222701015149704548103443727600) * 10 ^ 70 +
        5895078392180348981795355319446967886782733466427617964689951348052059) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 162 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 11 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_272_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (273 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_273 :
    recurrence2Scalar2Left.coeff 273 =
      -(((6650451264548169552259371941696340168223954194458073800075325151317 * 10 ^ 70 +
        0618121022478228584667127348409022542282058047717743833633549590291228) * 10 ^ 70 +
        8826384087534175025202134826218838471563430788316241229729523725929724) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 163 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 10 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_273_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (274 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_274 :
    recurrence2Scalar2Left.coeff 274 =
      (((2552984138627424132147363099118789472386501630899371822559967438867 * 10 ^ 70 +
        8382745232699342924267935942082284736009023435493027177042198761579266) * 10 ^ 70 +
        5893791041953821311601150020656584704312026867586640117314168659245293) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 164 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 9 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_274_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (275 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_275 :
    recurrence2Scalar2Left.coeff 275 =
      -(((899701160409480602060288097995151460906243155600267294076044796944 * 10 ^ 70 +
        3625506946771083152595266319768586767431605905041993784462616865983917) * 10 ^ 70 +
        6650550194573493184625033024827577993725898679066996603590514017783347) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 165 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 8 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_275_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (276 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_276 :
    recurrence2Scalar2Left.coeff 276 =
      (((282023394451165310390027896686579310843036052466122651312640233375 * 10 ^ 70 +
        2990561565081505615660069598111299824454006865615604890240912311543811) * 10 ^ 70 +
        5971975245321719960066686818139107228515155681146023533197840104376895) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 166 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 7 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_276_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (277 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_277 :
    recurrence2Scalar2Left.coeff 277 =
      -(((72596988485396502805635399159477456066817563479716560372510772388 * 10 ^ 70 +
        1219965727638192585228860039495528051457625858690590428896184042281778) * 10 ^ 70 +
        6958637097485085432187518385076105593673684835758890743237080016175428) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 167 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 6 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_277_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (278 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_278 :
    recurrence2Scalar2Left.coeff 278 =
      (((10958749170513135545560811139204749613060842470178004584335674091 * 10 ^ 70 +
        9761599044199857577383852829204906635130687888187324875312988755248639) * 10 ^ 70 +
        8478754347280960476769749662306570555119073042226371712249741779407952) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 168 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 5 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_278_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (279 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_279 :
    recurrence2Scalar2Left.coeff 279 =
      (((2862646354922322995973521962883823474717370463160601309493703218 * 10 ^ 70 +
        1077758132588223284064557085372203333911715097331998640161772649038851) * 10 ^ 70 +
        8777330983453031763352063052958350740646698748355277140280106955360423) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 169 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 4 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_279_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (280 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_280 :
    recurrence2Scalar2Left.coeff 280 =
      -(((3735844766505204283162981168593163073157035728176026640962657191 * 10 ^ 70 +
        8194088438870881045975312857613727779918691974682062032316545185143533) * 10 ^ 70 +
        2907743819346485631759064236733944864996221433167482279778170717630969) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 170 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 3 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_280_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (281 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_281 :
    recurrence2Scalar2Left.coeff 281 =
      (((2303656156191863267359386895618516041666526133065963858079194097 * 10 ^ 70 +
        2435294768400108043774638493412026268871647078901123091556539317783599) * 10 ^ 70 +
        8626333354308819061493167745518094918149341191023682255100377578101927) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 171 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 2 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_281_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (282 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_282 :
    recurrence2Scalar2Left.coeff 282 =
      -(((1128082207870393640408135721162305053984981849931798332563383500 * 10 ^ 70 +
        1380506842427586311650112416476337127158270132508587716719959475067561) * 10 ^ 70 +
        8552832415414056446635137556991847931421194854220483320877219508041171) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 172 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
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
    rw [show 15 = 1 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_282_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (283 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_283 :
    recurrence2Scalar2Left.coeff 283 =
      (((483982186868455425748734712907416562685593111422080561169766731 * 10 ^ 70 +
        6682327733001383885467358489201682981365909851501973843268178677145433) * 10 ^ 70 +
        7139188223036759370313413732256222872360337650756201477096275457711650) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 173 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 32 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_283_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (284 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_284 :
    recurrence2Scalar2Left.coeff 284 =
      -(((188419578099302611421047342238643968386123602053279818918880193 * 10 ^ 70 +
        9473622145457443458531777998234000055059451631110021145015888345732173) * 10 ^ 70 +
        8825706685156735187087022643586336871444056328178910332283764566410944) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 174 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 31 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_284_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (285 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_285 :
    recurrence2Scalar2Left.coeff 285 =
      (((67571867301490273694528260317768000400811986196866055122759656 * 10 ^ 70 +
        8377113632296049445544335604667648462868217989686067021626745728242366) * 10 ^ 70 +
        7830121263758402394846072983946318699536139121603988114716525263817961) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 175 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 30 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_285_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (286 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_286 :
    recurrence2Scalar2Left.coeff 286 =
      -(((22455794779591080576398713939573731991844355921083982398911747 * 10 ^ 70 +
        6418764794805774754198346843154062035523202607635843260497863157548220) * 10 ^ 70 +
        9215309189186087631094914212309370726501073843808401625900424763198404) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 176 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 29 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_286_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (287 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_287 :
    recurrence2Scalar2Left.coeff 287 =
      (((6916832439593875022854386517176893700067669071183804073781438 * 10 ^ 70 +
        5143342449917937436832062730616502646916420267985490206399051266655386) * 10 ^ 70 +
        7297429224304453516934557115905656346713289277405719845631936137726517) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 177 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 28 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_287_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (288 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_288 :
    recurrence2Scalar2Left.coeff 288 =
      -(((1964723198218348619018996914022181438230618457332696439260387 * 10 ^ 70 +
        0145483107980094242800310743648730045228085161629259800791064401488510) * 10 ^ 70 +
        0701060375288500055219726862279543372019529219593035836827832172443135) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 178 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 27 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_288_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (289 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_289 :
    recurrence2Scalar2Left.coeff 289 =
      (((508327318691584257513614362877159426411846728899222819241668 * 10 ^ 70 +
        3953935873638015227655201877162604869048171691850219071475646824359606) * 10 ^ 70 +
        7880598339831077800311530875466207538799173316184984478496797441406423) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 179 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 26 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_289_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (290 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_290 :
    recurrence2Scalar2Left.coeff 290 =
      -(((116659566775793600102829623727546197398752093763060364855476 * 10 ^ 70 +
        2660270471494121708379079115379984601514242563353341347818070000440250) * 10 ^ 70 +
        2079163416919828552973282089682270365141009421705508863720199768902003) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 180 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 25 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_290_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (291 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_291 :
    recurrence2Scalar2Left.coeff 291 =
      (((22265891157163054047844412710910237775242269399815171091500 * 10 ^ 70 +
        7600328750187964795132319749063766313457553065264768049364631550502879) * 10 ^ 70 +
        5562224238142381927988120001826618088017373844649694474231242022723190) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 181 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 24 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_291_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (292 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_292 :
    recurrence2Scalar2Left.coeff 292 =
      -(((2801360093301985412250015427885369642024878724974540547173 * 10 ^ 70 +
        1697853892346426211637940284372087669807567349701805546574427411085948) * 10 ^ 70 +
        4062303255119357557845322748384013198288060978543728679319144578111597) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 182 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 23 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_292_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (293 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_293 :
    recurrence2Scalar2Left.coeff 293 =
      -(((186098020529858540701799266179606616046214039679207424858 * 10 ^ 70 +
        0150616317545651079392201463619553421924908070579654834097710704650929) * 10 ^ 70 +
        9694303843240807521609695094303769951863375549642832953433399082922708) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 183 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 22 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_293_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (294 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_294 :
    recurrence2Scalar2Left.coeff 294 =
      (((287616063192653576593960078543851837089868127431046487700 * 10 ^ 70 +
        3825663580987589200073121978176759771146990152849798548071010221455839) * 10 ^ 70 +
        6614587448725964317375683115194933029375556556519814544194548374567133) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 184 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 21 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_294_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (295 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_295 :
    recurrence2Scalar2Left.coeff 295 =
      -(((127741103707792504867696752779089594665504292157696457215 * 10 ^ 70 +
        1580681019315809928235773165936256828265350457926788363092783979622658) * 10 ^ 70 +
        7345039328010944674006377133090458089981754512400345044817218649643763) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 185 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 20 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_295_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (296 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_296 :
    recurrence2Scalar2Left.coeff 296 =
      (((42483084601076049248025347753164726266707742842239577144 * 10 ^ 70 +
        8471488233519559110719246550719490075497296628120036940351152994609295) * 10 ^ 70 +
        4163490465321024968190376075953838423547070729127057989852919785476483) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 186 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 19 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_296_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (297 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_297 :
    recurrence2Scalar2Left.coeff 297 =
      -(((11978756424162249396720527522431273938403778817294423562 * 10 ^ 70 +
        2211526767137543737784611662293764216788906528990131010132143280205768) * 10 ^ 70 +
        0203799536365612396740724423017277693181891145600733499734053128226333) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 187 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 18 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_297_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (298 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_298 :
    recurrence2Scalar2Left.coeff 298 =
      (((2973189705221168828693456714760794845540513526372774966 * 10 ^ 70 +
        1369236900715496825144541878611674600410547592401554533688338079123587) * 10 ^ 70 +
        1316572366274756121573513033952456020527249406255097184707514051732482) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 188 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 17 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_298_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (299 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_299 :
    recurrence2Scalar2Left.coeff 299 =
      -(((656216470122983872287573079808537642144608597346658890 * 10 ^ 70 +
        1383325125106790819603193742494070767644120639804112869809790208872511) * 10 ^ 70 +
        7812749555577828838982854818928817614994619175380750464858865544370582) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 189 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 16 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_299_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (300 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_300 :
    recurrence2Scalar2Left.coeff 300 =
      (((127987718661675486541966266636279306833005924883990580 * 10 ^ 70 +
        5585333612261965108814268836148285027769487009341981984561829307312449) * 10 ^ 70 +
        1572035772211896767321903725867968650596419403185774154315830015836830) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 190 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 15 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_300_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (301 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_301 :
    recurrence2Scalar2Left.coeff 301 =
      -(((21479449134845973702037846328376245312179923357275133 * 10 ^ 70 +
        9166668032760308383204801394091587405275885204385341329971464610349092) * 10 ^ 70 +
        8150246118730315631340987439607754005327882880584185829868461641113820) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 191 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 14 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_301_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (302 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_302 :
    recurrence2Scalar2Left.coeff 302 =
      (((2874866375870631189101967707687495936845888080609990 * 10 ^ 70 +
        9304023408767000636634589402738522563433136715841361424685943026154410) * 10 ^ 70 +
        0801745853438272848199970055607156929712098335208327807503851076243972) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 192 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 13 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_302_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (303 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_303 :
    recurrence2Scalar2Left.coeff 303 =
      -(((222756117590763750190336552654529825418458199041235 * 10 ^ 70 +
        5429941804328850457104696808313917390101351538198327909008426115509971) * 10 ^ 70 +
        6665012173051740520017493044618978498709291476140364531623614627101972) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 193 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 12 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (304 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_304 :
    recurrence2Scalar2Left.coeff 304 =
      -(((25267707342556567618060670547252174032493324174661 * 10 ^ 70 +
        8053022986011846762238945259962982977429061875531556526074958207403703) * 10 ^ 70 +
        5425492374075220324735179309721609415498294354047615090099440598058048) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 194 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 11 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
