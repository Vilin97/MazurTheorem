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

private theorem recurrence2Scalar3Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (303 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_303 :
    recurrence2Scalar3Left.coeff 303 =
      (((761253957327360251865539841489674295705706619816 * 10 ^ 70 +
        9613348330076283406904244364788901772595126976345778917979056683235529) * 10 ^ 70 +
        2404495082299311192685774607361545260142145716247969848069332678208923) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 197 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 8 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_303_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (304 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_304 :
    recurrence2Scalar3Left.coeff 304 =
      -(((41062380566367415104769031419134473970385827574 * 10 ^ 70 +
        0490845816884440294228333434364037757931356014503642853947324129801561) * 10 ^ 70 +
        4346541983533101763571687700186471562553386341654861761968359188712614) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 198 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 7 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_304_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (305 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_305 :
    recurrence2Scalar3Left.coeff 305 =
      -(((10439252697784147358848459005609443627366025402 * 10 ^ 70 +
        6172251118619130994264805022850724177838677522208140447337246277188438) * 10 ^ 70 +
        8458530680099367728565704436838966526680655151326649112283059215740858) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 199 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 6 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (306 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_306 :
    recurrence2Scalar3Left.coeff 306 =
      (((4403284776164745346343472048074727662720991295 * 10 ^ 70 +
        3977183550604806584212922795176202976887237984590506426145533155838339) * 10 ^ 70 +
        6021309710090222495921063255601076468348102285635002974890351428145105) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 200 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 5 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (307 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_307 :
    recurrence2Scalar3Left.coeff 307 =
      -(((1027032763920642365499380203607936393875457072 * 10 ^ 70 +
        0769577200943508667092476728278951121352736643575779126865675551951837) * 10 ^ 70 +
        1185161299545312966398108562452970185243622603009130273247476369068301) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 201 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 4 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (308 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_308 :
    recurrence2Scalar3Left.coeff 308 =
      (((183644779003979565813202030697677723099243981 * 10 ^ 70 +
        5528725967684921236486111554993299897515023128667603837383721040139873) * 10 ^ 70 +
        5216508132380290999004845726685770565356333960512662488707167958055221) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 202 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 3 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (309 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_309 :
    recurrence2Scalar3Left.coeff 309 =
      -(((26725701864717119057766413647664650127020384 * 10 ^ 70 +
        6150283837648040594996849888868813721248400565529105879870118257009122) * 10 ^ 70 +
        2353293719002216682618319380460240932904384638247493104302526884330333) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 203 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 2 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (310 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_310 :
    recurrence2Scalar3Left.coeff 310 =
      (((3134460587360472089986630987896674327194796 * 10 ^ 70 +
        2779059369323956578986702649454216519726467523130420901427482498290993) * 10 ^ 70 +
        8133503995774707891606766719165787430946246972917017322747343851220656) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 204 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 43 = 1 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (311 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_311 :
    recurrence2Scalar3Left.coeff 311 =
      -(((269269524859673164731720647590863699125813 * 10 ^ 70 +
        5785755473501845417425362808767632787953309942905628220462295914567942) * 10 ^ 70 +
        3730802449513674372138661436741204446026036068452180355354538335923501) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 205 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 32 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (312 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_312 :
    recurrence2Scalar3Left.coeff 312 =
      (((9172472325275084848152228239317227073725 * 10 ^ 70 +
        6673207490125331151026586735951630509999931764260242682521178155565983) * 10 ^ 70 +
        5141445761550192739297001252525857000754116936714444635740135341957880) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 206 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 31 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (313 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_313 :
    recurrence2Scalar3Left.coeff 313 =
      (((2201818704035461563360984788751648823520 * 10 ^ 70 +
        5350564976012306966617595229723056082168571882103531839128615799145377) * 10 ^ 70 +
        9393982545472379639087055841938581035217233170449634693595475920732268) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 207 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 30 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (314 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_314 :
    recurrence2Scalar3Left.coeff 314 =
      -(((601828460418977312534619493122850825388 * 10 ^ 70 +
        9036144926869662474963934892786899010773383840656112478181371949057593) * 10 ^ 70 +
        8622420234675904642656844697998725477510070026961296991676304523283167) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 208 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 29 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (315 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_315 :
    recurrence2Scalar3Left.coeff 315 =
      (((92986694166813120889269668839887835087 * 10 ^ 70 +
        5355391372163833875268557329872481111792460871053585552089528752942155) * 10 ^ 70 +
        3503242982125951123002661126249098565896950692717008654803590868732497) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 209 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 28 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (316 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_316 :
    recurrence2Scalar3Left.coeff 316 =
      -(((10692630785927242785415202690266844314 * 10 ^ 70 +
        6626273743111233868434757936947445944693270212656968673764442796875303) * 10 ^ 70 +
        6428802303508110335848885244415674251930510530173931825776437110405224) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 210 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 27 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (317 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_317 :
    recurrence2Scalar3Left.coeff 317 =
      (((943149179684673184959324392451358582 * 10 ^ 70 +
        6186788389357899657105601519425229041238321192264796497114719089492705) * 10 ^ 70 +
        8258300950107758457903661302349115184827841267995116339153301743636562) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 211 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 26 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (318 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_318 :
    recurrence2Scalar3Left.coeff 318 =
      -(((58424696551278950177579529354558008 * 10 ^ 70 +
        1352362021630623565014521241378092437469310453248254077085848506510017) * 10 ^ 70 +
        6708093844147214262975683616640585183188636592486226008529833194778182) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 212 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 25 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (319 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_319 :
    recurrence2Scalar3Left.coeff 319 =
      (((1287342362845006016604961380305224 * 10 ^ 70 +
        2778110365415998578669571620927917184020228056850822401727122117672626) * 10 ^ 70 +
        0775740831948844746706968775114967262332128061208699599894465494279163) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 213 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 24 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (320 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_320 :
    recurrence2Scalar3Left.coeff 320 =
      (((251805025000276477040963575021860 * 10 ^ 70 +
        4328883662681218777223493368043918029406352541896056164417924920086158) * 10 ^ 70 +
        8098587714666393053371730340709953609374285352303295955151016584432169) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 214 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 23 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (321 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_321 :
    recurrence2Scalar3Left.coeff 321 =
      -(((43975537118395584560205317241023 * 10 ^ 70 +
        4451179525494425891123724517193963115475100649426576741059446006695375) * 10 ^ 70 +
        4294519372988077692874570862489804995697710836047236030132954753369284) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 215 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 22 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (322 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_322 :
    recurrence2Scalar3Left.coeff 322 =
      (((4237559802710584179119951761504 * 10 ^ 70 +
        7283295556598931651901248749232756038964543356740971183478986717106754) * 10 ^ 70 +
        3595272182976270470273927926247404989762526755607044945172090097482244) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 216 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 21 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (323 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_323 :
    recurrence2Scalar3Left.coeff 323 =
      -(((282906060721801625513745995596 * 10 ^ 70 +
        1717737970774161167504417174767065664906595187713034176717063923158947) * 10 ^ 70 +
        0109145840149472569176578273630604264618308307160739070110645805596690) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 217 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 20 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (324 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_324 :
    recurrence2Scalar3Left.coeff 324 =
      (((12277026976628213436952587580 * 10 ^ 70 +
        5960880093975788294671806872078102428072690849041031309584194445707144) * 10 ^ 70 +
        9602621275915761384718111828001968068996122077796901314556173373836203) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 218 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 19 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (325 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_325 :
    recurrence2Scalar3Left.coeff 325 =
      -(((138782822996129101447015301 * 10 ^ 70 +
        0283894890840495876567625095445908844626762020828908077656196857002196) * 10 ^ 70 +
        6489799778631997976429291369112586076951024488205978151304556645954219) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 219 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 18 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (326 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_326 :
    recurrence2Scalar3Left.coeff 326 =
      -(((29321053008182775096941201 * 10 ^ 70 +
        2893873133456601261165219053236879936101086558228780734361814230353960) * 10 ^ 70 +
        2018908302590179753664376649918877657556487980975878500496447357810789) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 220 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 17 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (327 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_327 :
    recurrence2Scalar3Left.coeff 327 =
      (((2961824897591133657308599 * 10 ^ 70 +
        0142734755194193507192385661266739589045205678135303594314562772558947) * 10 ^ 70 +
        8647583886252722631968693854640142997470008019122736518716391946109071) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 221 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 16 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (328 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_328 :
    recurrence2Scalar3Left.coeff 328 =
      -(((159689049752837257470476 * 10 ^ 70 +
        0936832677675100004988726964509304448424964992039098735977433351444447) * 10 ^ 70 +
        2242870570494862366648697498590712469094321697062788205023383468096610) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 222 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 15 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (329 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_329 :
    recurrence2Scalar3Left.coeff 329 =
      (((5051010503348827041956 * 10 ^ 70 +
        3173637394190690247611404741104040835280232938224296522684448387857908) * 10 ^ 70 +
        3047633187111043339292511225181289501663664148327812656683259471261932) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 223 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 14 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (330 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_330 :
    recurrence2Scalar3Left.coeff 330 =
      -(((36665764322236062650 * 10 ^ 70 +
        7260457231112352937449018642022680225857664286929653488691531710017317) * 10 ^ 70 +
        3260281583962541575463438310218460882003684650405706319777515459935533) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 224 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 13 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (331 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_331 :
    recurrence2Scalar3Left.coeff 331 =
      -(((5453410402168939914 * 10 ^ 70 +
        1408998785833780046207350370170065570712654850143409219942466469754429) * 10 ^ 70 +
        6032256793899071108221684969581293273026754935517008329033177165216348) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 225 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 12 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (332 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_332 :
    recurrence2Scalar3Left.coeff 332 =
      (((321115726500030422 * 10 ^ 70 +
        1680930341133258613839592075702995258316640748556422116337659528119481) * 10 ^ 70 +
        2075491849514132342852000629723271133944211025509038868144565938364643) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 226 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 11 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (333 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_333 :
    recurrence2Scalar3Left.coeff 333 =
      -(((8805971967721504 * 10 ^ 70 +
        9725452212470915083927102570010759232889209470394776077583416737757582) * 10 ^ 70 +
        2025098484297415608322643459715575631208304354474706667706478029623914) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 227 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 10 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (334 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_334 :
    recurrence2Scalar3Left.coeff 334 =
      (((81794875615493 * 10 ^ 70 +
        4187793055099502159356253086306382105154093390670825099179371355388998) * 10 ^ 70 +
        4873702602152140431326879718605050898389127117054231936103686227502607) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 228 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 9 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (335 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_335 :
    recurrence2Scalar3Left.coeff 335 =
      (((2887634848562 * 10 ^ 70 +
        3598338502890369755009191080306269186140230209546798638146484594003156) * 10 ^ 70 +
        6511824387225831188803095295976336508083834819848475461241009811262942) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 229 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 8 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar3Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 230,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient3.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A3_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar3Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient3.coeff (336 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar3Left_coeff_336 :
    recurrence2Scalar3Left.coeff 336 =
      -(((121207045541 * 10 ^ 70 +
        9291131149536822432029818382807876972674871639841569553653614644254585) * 10 ^ 70 +
        9190911733303274606697843215018008761285266624773687946415586256625035) : ℚ) := by
  unfold recurrence2Scalar3Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 230 +
    107 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 7 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar3Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar3Left_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
