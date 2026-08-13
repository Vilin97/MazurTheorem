/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA2
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar2LeftPart0Simp
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

private theorem recurrence2Scalar2Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 78,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_188 :
    recurrence2Scalar2Left.coeff 188 =
      (((421030363238423056520192766554587130075214632351462289436165 * 10 ^ 70 +
        3252336589113933178534256770894235383545425071783490326542758947612865) * 10 ^ 70 +
        4464704038359863552483044490608657127489109626387100262207040159807937) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 78 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_188_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_189_prefix_zero :
    (∑ x ∈ Finset.range 79,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (189 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (189 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_189 :
    recurrence2Scalar2Left.coeff 189 =
      -(((1083885563763864598375234377965080853781755834477934988463523 * 10 ^ 70 +
        0607795464334666032977121235600631847078456401629412080305723889829822) * 10 ^ 70 +
        8496964838063060046155275188911343594258930734768161006839600324298114) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 190 = 79 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_189_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_190_prefix_zero :
    (∑ x ∈ Finset.range 80,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (190 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (190 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_190 :
    recurrence2Scalar2Left.coeff 190 =
      (((1252633719980669760282330992626439267973457824210331589009407 * 10 ^ 70 +
        9183803746016012636798607474497736423893836898083973541799023665862092) * 10 ^ 70 +
        4085560973121810034592439586991416358290147666083009072846982764304621) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 191 = 80 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_190_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_191_prefix_zero :
    (∑ x ∈ Finset.range 81,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (191 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (191 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_191 :
    recurrence2Scalar2Left.coeff 191 =
      (((2601359834960894035565276555476515713928468358675834409047427 * 10 ^ 70 +
        0912369717462264701881298476524930071490299840989902997421260742042486) * 10 ^ 70 +
        1396660965184017312185788367385850922773114722874570944561204355921429) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 192 = 81 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_191_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_192_prefix_zero :
    (∑ x ∈ Finset.range 82,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (192 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (192 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_192 :
    recurrence2Scalar2Left.coeff 192 =
      -(((18565411944268601602757903882721704691645909496456403508194554 * 10 ^ 70 +
        7029842426191404646154640810219934730523186722618274507735069787277171) * 10 ^ 70 +
        0255409033483849698554838097056974699785633379180246673222157191896075) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 193 = 82 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_192_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_193_prefix_zero :
    (∑ x ∈ Finset.range 83,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (193 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (193 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_193 :
    recurrence2Scalar2Left.coeff 193 =
      (((54803225669087922040438778697769503315782611918062783560595364 * 10 ^ 70 +
        3672748000505227634071078213156588378272291956164150642249760481043809) * 10 ^ 70 +
        3093042402627709093826712071502696597563199568362565133607893531911169) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 194 = 83 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_193_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_194_prefix_zero :
    (∑ x ∈ Finset.range 84,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (194 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (194 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_194 :
    recurrence2Scalar2Left.coeff 194 =
      -(((91758650994382413851970728638935845536679403059823944657171214 * 10 ^ 70 +
        9276381712652122151778096129877185037154365715796827048690471455998436) * 10 ^ 70 +
        0905504311875110434361948474728718824044949416280000377009646691471503) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 195 = 84 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_194_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_195_prefix_zero :
    (∑ x ∈ Finset.range 85,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (195 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (195 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_195 :
    recurrence2Scalar2Left.coeff 195 =
      (((5525790677238454404954722157159567056492259710539258405293571 * 10 ^ 70 +
        3655214574417118595125703496243916964450194370353736022879380004794086) * 10 ^ 70 +
        9001319457885028494744294196954852083165543443011020756982519175167692) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 196 = 85 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_195_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_196_prefix_zero :
    (∑ x ∈ Finset.range 86,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (196 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (196 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_196 :
    recurrence2Scalar2Left.coeff 196 =
      (((555223852264301364903366439794694036554139875814762701280009940 * 10 ^ 70 +
        4189079727197329649556086258229034427462888952001871340526534345113925) * 10 ^ 70 +
        5985601275870217378544942263814877040604958969319552696903916477212285) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 197 = 86 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_196_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_197_prefix_zero :
    (∑ x ∈ Finset.range 87,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (197 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (197 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_197 :
    recurrence2Scalar2Left.coeff 197 =
      -(((2190703120644147327005902276367318511211619171711784373130009419 * 10 ^ 70 +
        1084706068080730338802814599578107613514998536441552796655608014746940) * 10 ^ 70 +
        1139725463195743361239588309799940816180074710837686891310215803800883) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 198 = 87 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_197_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_198_prefix_zero :
    (∑ x ∈ Finset.range 88,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (198 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (198 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_198 :
    recurrence2Scalar2Left.coeff 198 =
      (((5147414691307532885617922078426242099062724227779087816724451415 * 10 ^ 70 +
        1824165698063501543665824334107584493533639503840346080899079572952809) * 10 ^ 70 +
        8255684892000541539411475848970235749283790333437522144725477722690272) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 199 = 88 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_198_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_199_prefix_zero :
    (∑ x ∈ Finset.range 89,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (199 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (199 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_199 :
    recurrence2Scalar2Left.coeff 199 =
      -(((6977458782192972728347503368990829768525319310899229194171085701 * 10 ^ 70 +
        3093992032618176580401779965233023349768315440384430392490151726213715) * 10 ^ 70 +
        0004331034304070320296242938360359136187180405299375435910018728861032) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 200 = 89 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_199_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_200_prefix_zero :
    (∑ x ∈ Finset.range 90,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (200 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (200 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_200 :
    recurrence2Scalar2Left.coeff 200 =
      -(((2898628754885016642366911644393164045361804908815472606616914466 * 10 ^ 70 +
        9333306191651858923502105143973446795583743250286049723736635345623139) * 10 ^ 70 +
        8299497426278274509847283301530331225383833339743889900347668020367114) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 201 = 90 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_200_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_201_prefix_zero :
    (∑ x ∈ Finset.range 91,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (201 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (201 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_201 :
    recurrence2Scalar2Left.coeff 201 =
      (((51097924131711445566949807537771669114589844091892564356373501690 * 10 ^ 70 +
        7639931140607431079286532637206057613448252191262189591865691511214301) * 10 ^ 70 +
        1627249296618010979074810161436551059989126642451362400675546910197214) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 202 = 91 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_201_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_202_prefix_zero :
    (∑ x ∈ Finset.range 92,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (202 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (202 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_202 :
    recurrence2Scalar2Left.coeff 202 =
      -(((181893344063331811699880536232615189068416232145608203570697630694 * 10 ^ 70 +
        4225267478677348250149395991531704279282896284517683076429396798153508) * 10 ^ 70 +
        9877711193562876880708004974832070491405835156499060947844504032438491) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 203 = 92 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_202_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_203_prefix_zero :
    (∑ x ∈ Finset.range 93,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (203 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (203 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_203 :
    recurrence2Scalar2Left.coeff 203 =
      (((424347077915538285935850384989397233318104177014299054011287457008 * 10 ^ 70 +
        5241225705704989874477378070010474861603931732783636655721965331951454) * 10 ^ 70 +
        5289556280152740168946546608304436597758715060399983997279476259180624) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 204 = 93 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_203_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_204_prefix_zero :
    (∑ x ∈ Finset.range 94,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (204 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (204 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_204 :
    recurrence2Scalar2Left.coeff 204 =
      -(((664836516616577662539826691871877725678431141413549322303663689132 * 10 ^ 70 +
        4872788137811815211323855666741719723617796861786479109243650144990948) * 10 ^ 70 +
        6741170340160894563321140678269322821172579746630284712241946777856019) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 205 = 94 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_204_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_205_prefix_zero :
    (∑ x ∈ Finset.range 95,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (205 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (205 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_205 :
    recurrence2Scalar2Left.coeff 205 =
      (((337058128217924885483721210535085278605579275973561891670636686458 * 10 ^ 70 +
        6748966092163764056585803742042999066970477435740621861671843369449295) * 10 ^ 70 +
        0914972162086598680351608900068586983119203309993430140606713030258304) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 206 = 95 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_205_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_206_prefix_zero :
    (∑ x ∈ Finset.range 96,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (206 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (206 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_206 :
    recurrence2Scalar2Left.coeff 206 =
      (((2123026234303927352759508653358507312339641692086479590622682059716 * 10 ^ 70 +
        7252284687900474265226622904871235083359058766150961101094792723028692) * 10 ^ 70 +
        9178642701279145111519057365624721292380657810585844858924677415289679) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 207 = 96 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_206_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_207_prefix_zero :
    (∑ x ∈ Finset.range 97,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (207 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (207 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_207 :
    recurrence2Scalar2Left.coeff 207 =
      -(((9880428880730925352224428025641010855720819890663902187132057599150 * 10 ^ 70 +
        9737932061298658270702993144173916294219159825872314436681553266589996) * 10 ^ 70 +
        6547280319240407013157223210583774371444225585399036111088030602598347) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 208 = 97 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_207_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_208_prefix_zero :
    (∑ x ∈ Finset.range 98,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (208 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (208 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_208 :
    recurrence2Scalar2Left.coeff 208 =
      (((27548941658919795484766992188427575301666706950703536690146211983882 * 10 ^ 70 +
        0219554465359382437827663410826480135232652425432663985252844385942554) * 10 ^ 70 +
        9758481943720287173346533205095710888464398062384291529834912932941646) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 209 = 98 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_208_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_209_prefix_zero :
    (∑ x ∈ Finset.range 99,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (209 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (209 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_209 :
    recurrence2Scalar2Left.coeff 209 =
      -(((58185458826324368548684690022676179426246195393216481564254682796439 * 10 ^ 70 +
        2445092393480140947535470708664679906204102083633846702271472932553003) * 10 ^ 70 +
        9145905999929403295080189627410438670069203243684131824987236482782023) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 210 = 99 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_209_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_210_prefix_zero :
    (∑ x ∈ Finset.range 100,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (210 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (210 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_210 :
    recurrence2Scalar2Left.coeff 210 =
      (((93317754522990359827336921298257567556509715644826790414777144571300 * 10 ^ 70 +
        5905582248193069066254876908370778364451249069582063111857812468661932) * 10 ^ 70 +
        5184423491520223100029498725754508706057383380467122366351191552592315) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 211 = 100 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_210_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_211_prefix_zero :
    (∑ x ∈ Finset.range 101,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (211 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (211 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_211 :
    recurrence2Scalar2Left.coeff 211 =
      -(((89577553968500354540542648532051162340485477460567016580643834442868 * 10 ^ 70 +
        9008845118519311126245783018595934967004538124307742206002500424030901) * 10 ^ 70 +
        4993243673199038397317339737698165380581140710369275259462330310671605) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 212 = 101 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_211_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_212_prefix_zero :
    (∑ x ∈ Finset.range 102,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (212 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (212 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_212 :
    recurrence2Scalar2Left.coeff 212 =
      -(((75680435902013736665091813891405743322492613329469526763296446921286 * 10 ^ 70 +
        6280804131415209854593015131249726255848162934472634535976868775275470) * 10 ^ 70 +
        2169505215809405998973835158882807311761804701661997271718899707921826) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 213 = 102 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_212_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_213_prefix_zero :
    (∑ x ∈ Finset.range 103,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (213 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (213 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_213 :
    recurrence2Scalar2Left.coeff 213 =
      (((674658514920351674603570582190202736369572719333852803284244806914765 * 10 ^ 70 +
        0748007253941055308676529695948894754369350438972773221103141864732895) * 10 ^ 70 +
        0829224957242025209218160903583397355519995267351807564577383131438848) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 214 = 103 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_213_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_214_prefix_zero :
    (∑ x ∈ Finset.range 104,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (214 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (214 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_214 :
    recurrence2Scalar2Left.coeff 214 =
      -(((2219484412401583801548039240585648538114220600666675715670142799737767 * 10 ^ 70 +
        5951408759551591304044135941408110712837120699181812319229394237057111) * 10 ^ 70 +
        7495947863957759651896867727579486174311366030309274251547388682828098) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 215 = 104 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_214_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_215_prefix_zero :
    (∑ x ∈ Finset.range 105,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (215 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (215 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_215 :
    recurrence2Scalar2Left.coeff 215 =
      (((5544153222839494110779847547238510453570504485546778664485365471092768 * 10 ^ 70 +
        5769485380367959919477405679939664244659967190258822204156728619790501) * 10 ^ 70 +
        6381692072320374966068697199139707102548175650967223192880259400470503) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 216 = 105 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_215_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_216_prefix_zero :
    (∑ x ∈ Finset.range 106,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (216 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (216 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_216 :
    recurrence2Scalar2Left.coeff 216 =
      -((((1 * 10 ^ 70 +
        1813433047461844345429590447525820415437303437648850493341557390211774) * 10 ^ 70 +
        6304343126335043588830865014701541325694260179418385254163115696640400) * 10 ^ 70 +
        9771455655184633610355447222439899039856980996228960737062765654429133) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 217 = 106 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_216_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_217_prefix_zero :
    (∑ x ∈ Finset.range 107,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (217 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (217 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_217 :
    recurrence2Scalar2Left.coeff 217 =
      ((((2 * 10 ^ 70 +
        2349787457950717034463068690129776166927252868566710539515794452372571) * 10 ^ 70 +
        9185986724217578727322635949313192075368235070883977942005902484542574) * 10 ^ 70 +
        7695964684617997685165492725262476603942524322634556695784353976610500) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 218 = 107 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_217_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_218_prefix_zero :
    (∑ x ∈ Finset.range 108,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (218 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (218 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_218 :
    recurrence2Scalar2Left.coeff 218 =
      -((((3 * 10 ^ 70 +
        8132148053144114184338998574873997876645038397903163077210819643025267) * 10 ^ 70 +
        2431601317354125537830958570724702715828408286199127646942373912707792) * 10 ^ 70 +
        7233076385368719210160207626281684025547723549481272676784281695506994) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 219 = 108 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_218_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_219_prefix_zero :
    (∑ x ∈ Finset.range 109,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (219 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (219 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_219 :
    recurrence2Scalar2Left.coeff 219 =
      ((((5 * 10 ^ 70 +
        8816788731533780724059542519638842055462297758077176282490268859533820) * 10 ^ 70 +
        3063431750151011732976268803381044847347782537947715416184660893295184) * 10 ^ 70 +
        8013475818000339241673434186874998239353329319173229816957094818166868) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 220 = 109 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_219_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_220_prefix_zero :
    (∑ x ∈ Finset.range 110,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (220 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (220 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_220 :
    recurrence2Scalar2Left.coeff 220 =
      -((((8 * 10 ^ 70 +
        1193487211467436167892974827175864821793390723275529097643689603268056) * 10 ^ 70 +
        8083050718727734824361076850325298883613948307496826917680094753300368) * 10 ^ 70 +
        3571088798756508511626872865198417512081416395825466977108498576871936) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 221 = 110 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_220_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_221_prefix_zero :
    (∑ x ∈ Finset.range 111,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (221 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (221 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_221 :
    recurrence2Scalar2Left.coeff 221 =
      ((((9 * 10 ^ 70 +
        7146392363197202901798795312178158680069723127317269798229709720827526) * 10 ^ 70 +
        5392399240473155185022757894079617205895723089141339904520262870759031) * 10 ^ 70 +
        8116115690294654146434725873883981170690054135649325039749425969331581) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 222 = 111 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_221_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_222_prefix_zero :
    (∑ x ∈ Finset.range 112,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (222 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (222 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_222 :
    recurrence2Scalar2Left.coeff 222 =
      -((((9 * 10 ^ 70 +
        1440495936954417433500209057878506081500468122815741422949972709329131) * 10 ^ 70 +
        5368965657798752546847919531907149756953641192733170892892923646258868) * 10 ^ 70 +
        9351191611495873069658549931951742184520291300283990262815813298330403) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 223 = 112 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_222_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_223_prefix_zero :
    (∑ x ∈ Finset.range 113,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (223 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (223 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_223 :
    recurrence2Scalar2Left.coeff 223 =
      ((((3 * 10 ^ 70 +
        9959519264575106695104627166764902079509556938081873591121605554559305) * 10 ^ 70 +
        0083135856002072709115725120575919293396119741043152278619173550263506) * 10 ^ 70 +
        9346391540391387368002843343955010426543623460777776849082282089894330) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 224 = 113 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_223_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_224_prefix_zero :
    (∑ x ∈ Finset.range 114,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (224 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (224 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_224 :
    recurrence2Scalar2Left.coeff 224 =
      ((((9 * 10 ^ 70 +
        0714975477356887676301424866210539949165338696757803024349190918210703) * 10 ^ 70 +
        8141326805205784452046367268289626643634047150331756524233648646458763) * 10 ^ 70 +
        8933589773963504325543711425401873361466204948028125704225489673325111) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 225 = 114 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_224_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 115,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (225 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_225 :
    recurrence2Scalar2Left.coeff 225 =
      -((((34 * 10 ^ 70 +
        1404758193184122363254194868322103523138077312905664856451756177769133) * 10 ^ 70 +
        5893994791258703532682216093064232966421259364747818550319502148773052) * 10 ^ 70 +
        9808907804474107581427647511177582605596517829428541002423287501938282) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 226 = 115 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_225_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 116,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (226 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_226 :
    recurrence2Scalar2Left.coeff 226 =
      ((((75 * 10 ^ 70 +
        5359525086699658238091660860526474009143055872600690683618061936821164) * 10 ^ 70 +
        9340529105506086023403274820876897164592819022668221303005946721710904) * 10 ^ 70 +
        1688575036073648728011219956688561820063620639898568803214374080801730) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 227 = 116 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_226_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 117,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (227 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_227 :
    recurrence2Scalar2Left.coeff 227 =
      -((((137 * 10 ^ 70 +
        0054856523478242766962984994213619199854564434244658511595967586903225) * 10 ^ 70 +
        2373338681436806791425410668107611302183580389991873500461532387102947) * 10 ^ 70 +
        7764959255949313348497794493769075835216904872154330376410499128962355) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 228 = 117 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_227_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 118,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (228 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_228 :
    recurrence2Scalar2Left.coeff 228 =
      ((((220 * 10 ^ 70 +
        6558149713177888917574086087838209471504703065755017311278155347966816) * 10 ^ 70 +
        3105805968034382444311487042498758325384617491707763563980329329410990) * 10 ^ 70 +
        9259059706923259646248970649675133279394602050094776157919928471318615) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 229 = 118 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_228_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (229 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_229 :
    recurrence2Scalar2Left.coeff 229 =
      -((((325 * 10 ^ 70 +
        8336557734872387748048529270929643139291011300824764628506962460781970) * 10 ^ 70 +
        8274087161481791830378859741712472435689839782664735760602701693031514) * 10 ^ 70 +
        1545166593298915405726925213652467253145347716184060445813693567540816) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 230 = 119 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_229_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (230 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_230 :
    recurrence2Scalar2Left.coeff 230 =
      ((((448 * 10 ^ 70 +
        2258979594480589882697408762263130972355202942165778514417091762125736) * 10 ^ 70 +
        1775995259363731892457704629139618245711157101277645307252622052659651) * 10 ^ 70 +
        7895909202865186133151505820118216994731000171440836630702088905286381) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 231 = 120 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_230_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar2Left_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient2.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A2_coeff_high (231 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar2Left_coeff_231 :
    recurrence2Scalar2Left.coeff 231 =
      -((((579 * 10 ^ 70 +
        4841353490530810299539581995174919776368324860825032974829508888922945) * 10 ^ 70 +
        9004830771817012263715626872867342532532697222496150211957025956460230) * 10 ^ 70 +
        7636256573674859858211448965556909893530682378817556084778798397248716) : ℚ) := by
  unfold recurrence2Scalar2Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 232 = 121 +
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
    rw [show 15 = 15 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar2Left_coeff_231_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
