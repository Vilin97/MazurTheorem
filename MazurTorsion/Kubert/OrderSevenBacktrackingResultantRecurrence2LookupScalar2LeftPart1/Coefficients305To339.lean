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

private theorem recurrence2Scalar2Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (305 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_305 :
    recurrence2Scalar2Left.coeff 305 =
      (((16087760239018333980158038873770159108594768155804 * 10 ^ 70 +
        9285668820898670781046553417858002511148646737708885276902357660646957) * 10 ^ 70 +
        6083831233171466480861176183635879532562668677431012082331210316804492) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 195 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 10 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_305_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (306 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_306 :
    recurrence2Scalar2Left.coeff 306 =
      -(((4455661371919909605796074153788517877176365365925 * 10 ^ 70 +
        7644138935118422674685983669067318246608996933359537880267447161480401) * 10 ^ 70 +
        3865862996370770641390316601142924208089462562409412862267762496930317) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 196 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 9 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_306_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (307 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_307 :
    recurrence2Scalar2Left.coeff 307 =
      (((925535389616452272776775299712309472289989423719 * 10 ^ 70 +
        1497715069162997130650319533024990865702709386527659001302212842808738) * 10 ^ 70 +
        0422748839115422325466549624180178676607360082083887899358915012723981) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 197 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 8 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_307_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (308 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_308 :
    recurrence2Scalar2Left.coeff 308 =
      -(((156973418103484164225606627882256943570605412516 * 10 ^ 70 +
        8162593684631618182243505333568609043967397906676565052508292566083520) * 10 ^ 70 +
        1809523284743168816026774867127772670422352982788344003066132138836820) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 198 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 7 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_308_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (309 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_309 :
    recurrence2Scalar2Left.coeff 309 =
      (((21811217881162017561966725339793110067348971017 * 10 ^ 70 +
        2651847808719873428368147078430063237410601336489739231479557435567620) * 10 ^ 70 +
        2067005665244471732919938031897572888397583952807072166049938591901931) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 199 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 6 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (310 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_310 :
    recurrence2Scalar2Left.coeff 310 =
      -(((2325797623310376436658693188716378044320549337 * 10 ^ 70 +
        6266381261308068928762557368676566368363724865568039881510784485584591) * 10 ^ 70 +
        2759306002874843704723962519391222415811513542352998399736870436641398) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 200 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 5 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (311 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_311 :
    recurrence2Scalar2Left.coeff 311 =
      (((136647739161200651045149797600821545520484391 * 10 ^ 70 +
        9008566514898823315165599486169512804643967266737958733785907858343787) * 10 ^ 70 +
        1281654591058562025185170321742957307497446071327677512390037349766029) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 201 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 4 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (312 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_312 :
    recurrence2Scalar2Left.coeff 312 =
      (((13045677949910913888442157806857871137025892 * 10 ^ 70 +
        9733161959203757341048034716911887235742171075395293842715049615175930) * 10 ^ 70 +
        1051940697902288397481470217373433620794602995099675374783167961471624) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 202 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 3 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (313 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_313 :
    recurrence2Scalar2Left.coeff 313 =
      -(((5814437575274389327540463484239757488567911 * 10 ^ 70 +
        7442557862111217464706296115809139728579512755374391579226526443632575) * 10 ^ 70 +
        8544347759052424513798040655389308192706087938113986299977420688753067) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 203 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 2 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (314 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_314 :
    recurrence2Scalar2Left.coeff 314 =
      (((1129999732036585145876513791414335881948323 * 10 ^ 70 +
        0156564390090394022054025688228816075307259111599022487395572138358833) * 10 ^ 70 +
        8595560070002087466510072335712035705565856643575567514940359223245686) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 204 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 47 = 1 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (315 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_315 :
    recurrence2Scalar2Left.coeff 315 =
      -(((157010021059828247529828695111925925132334 * 10 ^ 70 +
        8644480273339799108004478359974924795715552693149156471433061410118566) * 10 ^ 70 +
        2254351780400617558569348110502447381420679006876841715615829641843801) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 205 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 32 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (316 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_316 :
    recurrence2Scalar2Left.coeff 316 =
      (((16258239816720147104185807193255100818037 * 10 ^ 70 +
        7701579331547910980041586147213971563108440693419785149731633449994394) * 10 ^ 70 +
        0121524512088547336531003570263763612915908428114696083466656635418055) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 206 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 31 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (317 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_317 :
    recurrence2Scalar2Left.coeff 317 =
      -(((1081868566915044865799843778097416190510 * 10 ^ 70 +
        1152764400497240809206938554880806812554342393050401852943760536758389) * 10 ^ 70 +
        7322824978249653531836432114911797156551239536703511678938965276698823) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 207 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 30 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (318 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_318 :
    recurrence2Scalar2Left.coeff 318 =
      -(((5603484325637920244322785348839540256 * 10 ^ 70 +
        6683117480096064880296611848914860956495351588458662804478748043068027) * 10 ^ 70 +
        3331524513144730424819611712693244146258442355973018931366225386608007) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 208 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 29 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (319 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_319 :
    recurrence2Scalar2Left.coeff 319 =
      (((14755256879065474541762386221694370962 * 10 ^ 70 +
        3040161338711425506055266232470729541504987559123069791088228528540051) * 10 ^ 70 +
        3568191520944972327796569929978833145296372025459908529188668028276019) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 209 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 28 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (320 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_320 :
    recurrence2Scalar2Left.coeff 320 =
      -(((2642262154490809006080408451161888674 * 10 ^ 70 +
        5081537125121599272328336667206662423056188076408183057711555060459706) * 10 ^ 70 +
        2485595807789231126679092706325785556654953347899339410617592865888644) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 210 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 27 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (321 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_321 :
    recurrence2Scalar2Left.coeff 321 =
      (((305323176573217965721892859798717706 * 10 ^ 70 +
        2461211442284665142770406952985644688322230710417189817096866602903292) * 10 ^ 70 +
        9045250827640743102666592531830106933787529764727824175006996352145729) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 211 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 26 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (322 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_322 :
    recurrence2Scalar2Left.coeff 322 =
      -(((25237946784593106777591955669402878 * 10 ^ 70 +
        0057354899652506520182714938271781740706992835865967607194869640781170) * 10 ^ 70 +
        7866488650408365021553567996440114034994585626973016828948642943145445) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 212 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 25 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (323 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_323 :
    recurrence2Scalar2Left.coeff 323 =
      (((1313236656696046941237318570940759 * 10 ^ 70 +
        6619078139681762685658364478968612999497767231884211625432575582297104) * 10 ^ 70 +
        8183516408045919496428804870217013024480206015795850521669408579623208) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 213 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 24 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (324 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_324 :
    recurrence2Scalar2Left.coeff 324 =
      (((1738826523886601189278588782436 * 10 ^ 70 +
        9532818985632791867786125923373467053947719605131486030257776279003927) * 10 ^ 70 +
        2870241125665255379255930807917652068904809130067039712036189841510176) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 214 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 23 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (325 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_325 :
    recurrence2Scalar2Left.coeff 325 =
      -(((9300957588039264729979674816363 * 10 ^ 70 +
        2162876027120660413584319856627098392958685898110994066666661255764355) * 10 ^ 70 +
        8736257792635631317643950538810295526950402422400581816509889218030199) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 215 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 22 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (326 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_326 :
    recurrence2Scalar2Left.coeff 326 =
      (((1193290370068103534739148347938 * 10 ^ 70 +
        1131939959983353183678650612195515430577133218372886841983561353092738) * 10 ^ 70 +
        6632437181894312028351937885371783119008308873345445831003991723482544) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 216 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 21 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (327 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_327 :
    recurrence2Scalar2Left.coeff 327 =
      -(((93810370870357213944997353633 * 10 ^ 70 +
        1111743789980645134973505117966586828140184775980578937053337283246243) * 10 ^ 70 +
        2626435596224305719768829704223768972340512444386153982142051180625485) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 217 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 20 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (328 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_328 :
    recurrence2Scalar2Left.coeff 328 =
      (((4870641262149088919892898330 * 10 ^ 70 +
        6772443745028041794199369913239767886301737433652954198082942467768206) * 10 ^ 70 +
        1331617615037230243202280109172211060770943129929183985273997558095672) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 218 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 19 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (329 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_329 :
    recurrence2Scalar2Left.coeff 329 =
      -(((118875454539409641969551200 * 10 ^ 70 +
        2801778841938210328093043431631510739208267729271846524210099652470886) * 10 ^ 70 +
        6313585505650102486770298734992352003015391185789280650138804635635468) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 219 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 18 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (330 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_330 :
    recurrence2Scalar2Left.coeff 330 =
      -(((5932370885721113589441815 * 10 ^ 70 +
        4100336578492916718169096965043495277920919647040839901487308836164001) * 10 ^ 70 +
        6491778523103845052698624624695953147156066950253356904746195641944724) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 220 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 17 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (331 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_331 :
    recurrence2Scalar2Left.coeff 331 =
      (((874200760887358420012534 * 10 ^ 70 +
        8945910192785023892722523824305791865278998468373005015924559113886768) * 10 ^ 70 +
        0379097909610616397108877860702589852608720354572912041637941716936628) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 221 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 16 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (332 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_332 :
    recurrence2Scalar2Left.coeff 332 =
      -(((53599993530036248586564 * 10 ^ 70 +
        1212165177743555782784784275730344681052218878455340997086454075295105) * 10 ^ 70 +
        6498737090398982518374923145619459786029267716929513085744391330518443) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 222 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 15 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (333 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_333 :
    recurrence2Scalar2Left.coeff 333 =
      (((1915264089749199042728 * 10 ^ 70 +
        7505120066604953498074527400089452226800815305572478226918955818208106) * 10 ^ 70 +
        7146500556477696511971300810587031288607377254712300807964466273314911) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 223 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 14 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (334 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_334 :
    recurrence2Scalar2Left.coeff 334 =
      -(((24864115081069586556 * 10 ^ 70 +
        5391911895619003621656791139359026561229292108370605585206750654593404) * 10 ^ 70 +
        6112675917276425008397059902742625443360029884353831888647749965972330) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 224 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 13 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (335 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_335 :
    recurrence2Scalar2Left.coeff 335 =
      -(((1475220983599919924 * 10 ^ 70 +
        2679072695426718174592400574546156617127016552537586424926566372659304) * 10 ^ 70 +
        0016362391214163116723773425233037834481185047065496346703726215738701) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 225 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 12 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (336 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_336 :
    recurrence2Scalar2Left.coeff 336 =
      (((105264925801848874 * 10 ^ 70 +
        9943561275080523127471693936597586652400261290338006148813984747706271) * 10 ^ 70 +
        5937304888973648237197458415022668584881833886131483010719278635699181) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 226 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 11 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (337 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_337 :
    recurrence2Scalar2Left.coeff 337 =
      -(((3172886036126776 * 10 ^ 70 +
        6349759271776894359650339091547233509708858736005370181444977789422946) * 10 ^ 70 +
        4833149945321765289596473456865036437339758252585612726680561271332018) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 227 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 10 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (338 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_338 :
    recurrence2Scalar2Left.coeff 338 =
      (((36970308084168 * 10 ^ 70 +
        1749555896864692057855549012113368134677854752359501778903845049043554) * 10 ^ 70 +
        9442541112782191850181475721211843281645342523645535956635718102659197) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 228 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 9 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 229,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar2Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient2.coeff (339 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_339 :
    recurrence2Scalar2Left.coeff 339 =
      (((803893015850 * 10 ^ 70 +
        8922187662053065059428633535503589508345448177535954528013423867070326) * 10 ^ 70 +
        9091102832308982211037647145413139695308800960008160364821125931221373) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 229 +
    111 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 8 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar2Left_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
