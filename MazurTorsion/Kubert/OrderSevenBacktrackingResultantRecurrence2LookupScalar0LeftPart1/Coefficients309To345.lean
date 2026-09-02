/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA0
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar0LeftPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar0Left coefficient convolution

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
  recurrence2A0_coeff_0
  recurrence2A0_coeff_1
  recurrence2A0_coeff_2
  recurrence2A0_coeff_3
  recurrence2A0_coeff_4
  recurrence2A0_coeff_5
  recurrence2A0_coeff_6
  recurrence2A0_coeff_7
  recurrence2A0_coeff_8
  recurrence2A0_coeff_9
  recurrence2A0_coeff_10
  recurrence2A0_coeff_11
  recurrence2A0_coeff_12
  recurrence2A0_coeff_13
  recurrence2A0_coeff_14
  recurrence2A0_coeff_15
  recurrence2A0_coeff_16
  recurrence2A0_coeff_17
  recurrence2A0_coeff_18
  recurrence2A0_coeff_19
  recurrence2A0_coeff_20
  recurrence2A0_coeff_21
  recurrence2A0_coeff_22
  recurrence2A0_coeff_23
  recurrence2A0_coeff_24
  recurrence2A0_coeff_25
  recurrence2A0_coeff_26
  recurrence2A0_coeff_27
  recurrence2A0_coeff_28
  recurrence2A0_coeff_29
  recurrence2A0_coeff_30
  recurrence2A0_coeff_31
  recurrence2A0_coeff_32
  recurrence2A0_coeff_33
  recurrence2A0_coeff_34
  recurrence2A0_coeff_35
  recurrence2A0_coeff_36
  recurrence2A0_coeff_37
  recurrence2A0_coeff_38
  recurrence2A0_coeff_39
  recurrence2A0_coeff_40
  recurrence2A0_coeff_41
  recurrence2A0_coeff_42
  recurrence2A0_coeff_43
  recurrence2A0_coeff_44
  recurrence2A0_coeff_45
  recurrence2A0_coeff_46
  recurrence2A0_coeff_47
  recurrence2A0_coeff_48
  recurrence2A0_coeff_49
  recurrence2A0_coeff_50
  recurrence2A0_coeff_51
  recurrence2A0_coeff_52
  recurrence2A0_coeff_53
  recurrence2A0_coeff_54
  recurrence2A0_coeff_55
  recurrence2A0_coeff_56
  recurrence2A0_coeff_57
  recurrence2A0_coeff_58
  recurrence2A0_coeff_59
  recurrence2A0_coeff_60
  recurrence2A0_coeff_61
  recurrence2A0_coeff_62
  recurrence2A0_coeff_63
  recurrence2A0_coeff_64
  recurrence2A0_coeff_65
  recurrence2A0_coeff_66
  recurrence2A0_coeff_67
  recurrence2A0_coeff_68
  recurrence2A0_coeff_69
  recurrence2A0_coeff_70
  recurrence2A0_coeff_71
  recurrence2A0_coeff_72
  recurrence2A0_coeff_73
  recurrence2A0_coeff_74
  recurrence2A0_coeff_75
  recurrence2A0_coeff_76
  recurrence2A0_coeff_77
  recurrence2A0_coeff_78
  recurrence2A0_coeff_79
  recurrence2A0_coeff_80
  recurrence2A0_coeff_81
  recurrence2A0_coeff_82
  recurrence2A0_coeff_83
  recurrence2A0_coeff_84
  recurrence2A0_coeff_85
  recurrence2A0_coeff_86
  recurrence2A0_coeff_87
  recurrence2A0_coeff_88
  recurrence2A0_coeff_89
  recurrence2A0_coeff_90
  recurrence2A0_coeff_91
  recurrence2A0_coeff_92
  recurrence2A0_coeff_93
  recurrence2A0_coeff_94
  recurrence2A0_coeff_95
  recurrence2A0_coeff_96
  recurrence2A0_coeff_97
  recurrence2A0_coeff_98
  recurrence2A0_coeff_99
  recurrence2A0_coeff_100
  recurrence2A0_coeff_101
  recurrence2A0_coeff_102
  recurrence2A0_coeff_103
  recurrence2A0_coeff_104
  recurrence2A0_coeff_105
  recurrence2A0_coeff_106
  recurrence2A0_coeff_107
  recurrence2A0_coeff_108
  recurrence2A0_coeff_109
  recurrence2A0_coeff_110
  recurrence2A0_coeff_111
  recurrence2A0_coeff_112
  recurrence2A0_coeff_113
  recurrence2A0_coeff_114
  recurrence2A0_coeff_115
  recurrence2A0_coeff_116
  recurrence2A0_coeff_117
  recurrence2A0_coeff_118

private theorem recurrence2Scalar0Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (309 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_309 :
    recurrence2Scalar0Left.coeff 309 =
      -(((712962873099537560374187841228764282319280473690977 * 10 ^ 70 +
        8844435594556174377119947966475031016773457264354599616965564776345761) * 10 ^ 70 +
        3878244708157871164715832310740781631386036021628251059131907382503343) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 191 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 14 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_309_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (310 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_310 :
    recurrence2Scalar0Left.coeff 310 =
      -(((12264364436915593515187237120153698001495300200604 * 10 ^ 70 +
        2743533861390257399537049213284567280760775492337117375202076785018530) * 10 ^ 70 +
        9026657986236607194756109683053713376067593848029322600709847713270527) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 192 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 13 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_310_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (311 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_311 :
    recurrence2Scalar0Left.coeff 311 =
      (((26733877445043090053021017976408944130743120178293 * 10 ^ 70 +
        4100997798023990539952999158928308610507151661407259264101288766864363) * 10 ^ 70 +
        4657848271894697582576087627609768677274038072354397412718657038363097) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 193 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 12 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_311_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (312 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_312 :
    recurrence2Scalar0Left.coeff 312 =
      -(((8284550868544655167606285717090721499841659087872 * 10 ^ 70 +
        8553969551543811383594166751989606324898507024330137071154641697864304) * 10 ^ 70 +
        4521720802511470759656454347398224507254777927888718815236188329858526) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 194 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 11 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_312_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (313 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_313 :
    recurrence2Scalar0Left.coeff 313 =
      (((1847661331918508174561333732266335081642824243033 * 10 ^ 70 +
        3411232299387669555955080798968493084022330403273502369300864140471732) * 10 ^ 70 +
        7196925113096043949495976517629522302954577924991412161948948597834381) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 195 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 10 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_313_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (314 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_314 :
    recurrence2Scalar0Left.coeff 314 =
      -(((343175472794464526948799310473127807372768033169 * 10 ^ 70 +
        8536561665142901897258323792833130790607352747884312823942444193990836) * 10 ^ 70 +
        2088878704761916281836484094765725530916756804313926221134943669434418) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 196 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 9 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_314_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (315 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_315 :
    recurrence2Scalar0Left.coeff 315 =
      (((55379129825453295911318901353116781182489827066 * 10 ^ 70 +
        7737382595968321927352926688470191433237770111919880575765727674316044) * 10 ^ 70 +
        4300372748600282266911781495921864504471037688373206026185942658721875) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 197 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 8 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_315_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (316 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_316 :
    recurrence2Scalar0Left.coeff 316 =
      -(((7848291173427261641914610215848601839396637977 * 10 ^ 70 +
        6657213134710602827204356482840337282497564280355895242107197005353812) * 10 ^ 70 +
        9489133861135769802741738501928944995986508416939122327312632358651350) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 198 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 7 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_316_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (317 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_317 :
    recurrence2Scalar0Left.coeff 317 =
      (((967339076056192062211058122078539914301116190 * 10 ^ 70 +
        8105579500496733652365268416571111167319830131054130131763124993298588) * 10 ^ 70 +
        8890700381039839384807475711664219132209697957940384258436264394975133) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 199 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 6 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_317_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (318 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_318 :
    recurrence2Scalar0Left.coeff 318 =
      -(((99556399345891246265946547571755902815731541 * 10 ^ 70 +
        0463820928499923380432893812899084716164023371785671644790090478987543) * 10 ^ 70 +
        5444407229391590149292198701044284688555873468864665753224027394435623) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 200 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 5 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_318_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (319 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_319 :
    recurrence2Scalar0Left.coeff 319 =
      (((7443756064830287147589435292702190514737787 * 10 ^ 70 +
        4394201308646465426984484099909496562849582666951522786501526625128811) * 10 ^ 70 +
        2169328829767090274396548866729798221869534125936263849731266046383161) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 201 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 4 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_319_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (320 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_320 :
    recurrence2Scalar0Left.coeff 320 =
      -(((107574314259787404500494314479812290076573 * 10 ^ 70 +
        3001304442184782888327447980237589917983853435940566654567594266958601) * 10 ^ 70 +
        6227117309777665479919706882606208063015001407030354830474632630678632) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 202 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 3 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_320_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (321 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_321 :
    recurrence2Scalar0Left.coeff 321 =
      -(((94603000283693962999864298631117375336937 * 10 ^ 70 +
        9454768483480598774936618943310160961736550709081779549042088112339919) * 10 ^ 70 +
        9429496421633346259938502293813117126480725130935985940007893919498699) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 203 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 2 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_321_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (322 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_322 :
    recurrence2Scalar0Left.coeff 322 =
      (((23126533298365890953945634367788197400776 * 10 ^ 70 +
        7445132615917295443803174991084436146216592866757280749199427365957789) * 10 ^ 70 +
        2604970998308944474207423949269803473521351242127934245215308930615927) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 204 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 55 = 1 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_322_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (323 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_323 :
    recurrence2Scalar0Left.coeff 323 =
      -(((3717451970750719365740929602494948098318 * 10 ^ 70 +
        6758118429903228123122238781622899638157199851159284578588670054574380) * 10 ^ 70 +
        4153082109016000596114459757357276880976677420201401918119551276383960) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 205 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 32 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_323_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (324 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_324 :
    recurrence2Scalar0Left.coeff 324 =
      (((474060458432510695705727790452460784489 * 10 ^ 70 +
        6155295560804926434504721916807468441373796857746052545933325578286793) * 10 ^ 70 +
        6609330451247941504628306834339755244743564364661327974211062427043778) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 206 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 31 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_324_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (325 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_325 :
    recurrence2Scalar0Left.coeff 325 =
      -(((49360163516387917409765693543920757769 * 10 ^ 70 +
        2104021297921792757407451521636766213115234226029001072003281473315959) * 10 ^ 70 +
        7189518213979376708822454150224703040994915825013694228152213663752883) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 207 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 30 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_325_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (326 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_326 :
    recurrence2Scalar0Left.coeff 326 =
      (((4031095699685929672625689051365031035 * 10 ^ 70 +
        4824021659353191184655637806680214463644384721421253585730357502020532) * 10 ^ 70 +
        1691180267720746117866822102808071189329062760343341151211698284013854) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 208 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 29 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_326_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (327 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_327 :
    recurrence2Scalar0Left.coeff 327 =
      -(((212574222187937997110349061246290100 * 10 ^ 70 +
        3501441487244692224632336449808558032945578950293488978242022951402526) * 10 ^ 70 +
        0284803163143519144381546828018071511068755358798978356637862516140147) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 209 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 28 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_327_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (328 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_328 :
    recurrence2Scalar0Left.coeff 328 =
      -(((2436934416261168005066180035820634 * 10 ^ 70 +
        2630656957700349934270667193710056115478107002674296362399644364983244) * 10 ^ 70 +
        0573694522727805195878450148935724382762932668052598611460951328064221) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 210 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 27 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_328_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (329 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_329 :
    recurrence2Scalar0Left.coeff 329 =
      (((2276908397891162044679189310621014 * 10 ^ 70 +
        6126982286713715086390827577259747607972033425252759194016393514018837) * 10 ^ 70 +
        6860994693743217238154894172634298169503903181436789788736598608808257) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 211 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 26 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_329_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (330 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_330 :
    recurrence2Scalar0Left.coeff 330 =
      -(((328000199020455480878410794994615 * 10 ^ 70 +
        3692697383158801701402553091457179087564818913499410786153256336582757) * 10 ^ 70 +
        8079795598906857969362026880416043431137248363520187503777367091600876) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 212 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 25 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_330_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (331 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_331 :
    recurrence2Scalar0Left.coeff 331 =
      (((30289266453481083047987681683454 * 10 ^ 70 +
        5192420908923345793156829412041193299613796573109532801435206422163705) * 10 ^ 70 +
        5372187810326948069233029169685778983229762777549408266159037306220983) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 213 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 24 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_331_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (332 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_332 :
    recurrence2Scalar0Left.coeff 332 =
      -(((1877565466017358150315406870413 * 10 ^ 70 +
        7273303939825340610418376311756744358292752115165034450585943070175148) * 10 ^ 70 +
        8257061776693460194594414820571144426548417441928390198756959519416086) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 214 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 23 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_332_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (333 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_333 :
    recurrence2Scalar0Left.coeff 333 =
      (((51938218172851430573973218944 * 10 ^ 70 +
        3734634440296300047667437339967947488398274928824318803216079386252584) * 10 ^ 70 +
        5453058312934622657510530499717464378816205687491223394394429257144562) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 215 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 22 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_333_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (334 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_334 :
    recurrence2Scalar0Left.coeff 334 =
      (((4327438710950299821951868937 * 10 ^ 70 +
        6275307830457282291960176288274549536381271987301728466326310201585977) * 10 ^ 70 +
        3760307617089374523917652358800626377789343760162407225801574246992400) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 216 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 21 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_334_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (335 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_335 :
    recurrence2Scalar0Left.coeff 335 =
      -(((750476104334396943556657867 * 10 ^ 70 +
        0731026664822022661757592555010043023592035214684071840974833056698808) * 10 ^ 70 +
        2401350957728846956928751263665522803281105561229929656231076677245003) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 217 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 20 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_335_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (336 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_336 :
    recurrence2Scalar0Left.coeff 336 =
      (((59347853580521987605126635 * 10 ^ 70 +
        9519826663423166588735270623665825457166513954421685688285332307700541) * 10 ^ 70 +
        4895429556879968398805332066564666493610408152135351864165148495156127) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 218 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 19 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_336_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (337 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_337 :
    recurrence2Scalar0Left.coeff 337 =
      -(((2796558143084206163998519 * 10 ^ 70 +
        2622771000069686896847216048190250143206818177069275064117842848333427) * 10 ^ 70 +
        7631400923800996633581841992312825764285146993775564580086410533846337) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 219 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 18 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_337_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (338 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_338 :
    recurrence2Scalar0Left.coeff 338 =
      (((44178320123045435906191 * 10 ^ 70 +
        6832291671091440564004707608711961340793807484898927781596068750480387) * 10 ^ 70 +
        3637859132658620029497639542782192505526812275228568339421168931166087) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 220 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 17 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_338_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (339 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_339 :
    recurrence2Scalar0Left.coeff 339 =
      (((4907344720404843491479 * 10 ^ 70 +
        2743351997742545161632276194934237692924151732699024294891025351691799) * 10 ^ 70 +
        6139367732896310915435009285816852099394904218441565639006227746178427) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 221 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 16 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_339_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (340 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_340 :
    recurrence2Scalar0Left.coeff 340 =
      -(((494219462829885113804 * 10 ^ 70 +
        7429452543483805472558517225927060119489932739701429870198869003891746) * 10 ^ 70 +
        2534906102650049350828980787342221750105745227377991754775398638904305) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 222 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 15 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_340_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (341 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_341 :
    recurrence2Scalar0Left.coeff 341 =
      (((23516903397011475492 * 10 ^ 70 +
        9814022138006174367482648981675391700452341334182933987821210760582501) * 10 ^ 70 +
        8578556763017035651396329290299390289381779860404483932413620857653341) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 223 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 14 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_341_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (342 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_342 :
    recurrence2Scalar0Left.coeff 342 =
      -(((550568247034722056 * 10 ^ 70 +
        2684324187440794783439940547229206780731207105480609615034309092966226) * 10 ^ 70 +
        1701707854510239589028277453647529759293905323336564497709692377505697) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 224 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 13 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_342_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_343_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (343 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (343 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_343_suffix_zero :
    (∑ x ∈ Finset.range 75,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (343 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_343 :
    recurrence2Scalar0Left.coeff 343 =
      -(((5732490478757103 * 10 ^ 70 +
        8633932084050728484170110615688300161123979792218303911581298124673250) * 10 ^ 70 +
        7925498374039214318693934792690873538806289250127551625490336932771063) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 344 = 225 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 12 +
      75 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_343_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_343_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_344_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (344 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (344 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_344_suffix_zero :
    (∑ x ∈ Finset.range 76,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (344 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_344 :
    recurrence2Scalar0Left.coeff 344 =
      (((991165877872832 * 10 ^ 70 +
        0821429387209375484822415480441219272011214143188471053806466308295721) * 10 ^ 70 +
        0718322112443478334898250270964540816191941883826103683253968232599781) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 345 = 226 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 11 +
      76 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_344_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_344_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar0Left_coeff_345_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient0.coeff (345 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A0_coeff_high (345 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar0Left_coeff_345_suffix_zero :
    (∑ x ∈ Finset.range 77,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient0.coeff (345 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar0Left_coeff_345 :
    recurrence2Scalar0Left.coeff 345 =
      -(((37460510214738 * 10 ^ 70 +
        1914458488732155291162844510124718789850432698854440119330637323173312) * 10 ^ 70 +
        5782222826185269523623708409991914956338366303387753575295715294508986) : ℚ) := by
  unfold recurrence2Scalar0Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 346 = 227 +
    119 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 10 +
      77 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar0Left_coeff_345_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar0Left_coeff_345_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
