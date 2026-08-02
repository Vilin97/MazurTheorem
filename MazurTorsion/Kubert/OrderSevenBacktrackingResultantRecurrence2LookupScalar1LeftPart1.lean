/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/

import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA1
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 2 lookup certificate: Scalar1Left coefficient convolution

This is a checked coefficient-lookup shard for the second
pseudo-division recurrence in the order-seven certificate.
-/

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

private theorem recurrence2Scalar1Left_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 119,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (233 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_233 :
    recurrence2Scalar1Left.coeff 233 =
      -((((3169 * 10 ^ 70 +
        8054496941105839786906928034247987481858394383048287606564522466940782) * 10 ^ 70 +
        0611566354671837828657257874844247154849792920490441289066687532369061) * 10 ^ 70 +
        4748385158473687212732992003280836094217871237384672880587519605026397) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 234 = 119 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_233_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 120,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (234 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_234 :
    recurrence2Scalar1Left.coeff 234 =
      ((((3745 * 10 ^ 70 +
        1065196659936343443196457775481947319436814105918276118469548568649521) * 10 ^ 70 +
        5135482349807200700432046771386096088565671423599034844882952749528774) * 10 ^ 70 +
        6054369537749525179713835828127229835346437619055632928569368355975872) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 235 = 120 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_234_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 121,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (235 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_235 :
    recurrence2Scalar1Left.coeff 235 =
      -((((4192 * 10 ^ 70 +
        5567610654861739732743231314721861663527278108156180773170151076437858) * 10 ^ 70 +
        9619154073798772554790993507533621777378077254767479517999101912557278) * 10 ^ 70 +
        5544638719317736058008638602322979621020302916863013008017498442551547) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 236 = 121 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_235_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 122,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (236 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_236 :
    recurrence2Scalar1Left.coeff 236 =
      ((((4446 * 10 ^ 70 +
        1821947140216617058066709115096758941030323318230179326837148260417803) * 10 ^ 70 +
        2986101780464096921237355301988178656834307307517149385949433523118355) * 10 ^ 70 +
        1891715237624709290532754578431877686342731449924815361664934887558188) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 237 = 122 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_236_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 123,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (237 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_237 :
    recurrence2Scalar1Left.coeff 237 =
      -((((4457 * 10 ^ 70 +
        4291969135953104181283828115163335036633956171839850097922843085336337) * 10 ^ 70 +
        4084784846195601228156531530625986322238114788893262997788506767155444) * 10 ^ 70 +
        9157399880701290159310933586666250879502840874845648346112833098725301) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 238 = 123 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_237_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 124,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (238 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_238 :
    recurrence2Scalar1Left.coeff 238 =
      ((((4205 * 10 ^ 70 +
        1045479275367687635037218169389401625750255140431508420648624729201464) * 10 ^ 70 +
        1915455212701178237864906267529890849027960974964284512925503868019301) * 10 ^ 70 +
        2382546669594668069411753097944293117100754015720414996526703888140345) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 239 = 124 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_238_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 125,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (239 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_239 :
    recurrence2Scalar1Left.coeff 239 =
      -((((3700 * 10 ^ 70 +
        9410286694357562064886175219950809659916229004394892388147038420360170) * 10 ^ 70 +
        4807029240770487458017154931283061171761871477735980120864822479193532) * 10 ^ 70 +
        2809116764906284709471623901763729073141408447671963066544902478067934) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 240 = 125 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_239_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 126,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (240 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_240 :
    recurrence2Scalar1Left.coeff 240 =
      ((((2989 * 10 ^ 70 +
        2715910794754190609658948265698479092045668226467403850520434602238381) * 10 ^ 70 +
        0900342321290884422752135676568021116439745874428960748583597840253722) * 10 ^ 70 +
        6656666836855436403400415630347385104316958364337565174143291829444469) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 241 = 126 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_240_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 127,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (241 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_241 :
    recurrence2Scalar1Left.coeff 241 =
      -((((2140 * 10 ^ 70 +
        6433124832439201908143088329383720673772849821271231936276599030855282) * 10 ^ 70 +
        7678842963559616522198747539459708200723800628454165222032711430292826) * 10 ^ 70 +
        3303491412148893159566294333016541248972922849151717726898009071037195) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 242 = 127 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_241_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 128,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (242 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_242 :
    recurrence2Scalar1Left.coeff 242 =
      ((((1240 * 10 ^ 70 +
        6411733802679561454508245800987779997557236801248359265367206582644150) * 10 ^ 70 +
        2864272077485930560761085514097965022071366808528913560428240361666685) * 10 ^ 70 +
        7253970164187545022682510152686036332223729992481540418947355228673588) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 243 = 128 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_242_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 129,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (243 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_243 :
    recurrence2Scalar1Left.coeff 243 =
      -((((376 * 10 ^ 70 +
        3098562362188636281520488783465814638627303016919306190981950272200038) * 10 ^ 70 +
        8635505269123552841689384583477579312131542633518023566379123214275120) * 10 ^ 70 +
        2681598789064655104053917149760857992739399914051641158117391914284026) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 244 = 129 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_243_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 130,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (244 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_244 :
    recurrence2Scalar1Left.coeff 244 =
      -((((376 * 10 ^ 70 +
        9543524425208381496695244564018682707868222254783903036488516954342731) * 10 ^ 70 +
        1414365009872438480598168636449882613909068445250939596882215154118246) * 10 ^ 70 +
        9590967483782745862671055213356192177716768043587601449661048937250955) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 245 = 130 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_244_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 131,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (245 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_245 :
    recurrence2Scalar1Left.coeff 245 =
      ((((965 * 10 ^ 70 +
        4339289209719667965775444187062256622673803988994994965136550062031309) * 10 ^ 70 +
        6600542985319743170151445495139782880490465793266282799784767435211252) * 10 ^ 70 +
        8337842075608420522637446458147865987241590236128714114897234987467941) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 246 = 131 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_245_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 132,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (246 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_246 :
    recurrence2Scalar1Left.coeff 246 =
      -((((1362 * 10 ^ 70 +
        3326622971737000021816950588724588271304654864301158061476685140052111) * 10 ^ 70 +
        1725584930892046242649834278524904782380405224014681636358400832660069) * 10 ^ 70 +
        3408620157376932037594268489634335541835566414972377999706381127708581) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 247 = 132 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_246_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 133,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (247 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_247 :
    recurrence2Scalar1Left.coeff 247 =
      ((((1567 * 10 ^ 70 +
        7567551416923528946686689512012325481842340321208806583732948494215608) * 10 ^ 70 +
        6737919318133621595995695040542264179864510361593842871873109479912015) * 10 ^ 70 +
        8757675325098055969961724554397497740224191094674715732233834202299612) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 248 = 133 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_247_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 134,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (248 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_248 :
    recurrence2Scalar1Left.coeff 248 =
      -((((1604 * 10 ^ 70 +
        1704957703785468016430237885057187492217075588815543783252645603826229) * 10 ^ 70 +
        7625253025673792676150255664888233649022804005050551410541627953888144) * 10 ^ 70 +
        4122577733937038202455270209275039996064245002710622198535143412941128) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 249 = 134 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_248_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 135,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (249 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_249 :
    recurrence2Scalar1Left.coeff 249 =
      ((((1508 * 10 ^ 70 +
        9293826798083757337823844548793779257664897958212207645629615559930729) * 10 ^ 70 +
        8208309260262303251169511774273394492452566443995982818710982983877824) * 10 ^ 70 +
        7801973757329629852460194481256735856258412811222688379255224177487126) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 250 = 135 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_249_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 136,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (250 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_250 :
    recurrence2Scalar1Left.coeff 250 =
      -((((1325 * 10 ^ 70 +
        8422172428782820562906444339549609389162112710388436631462699649952532) * 10 ^ 70 +
        4857479887044460967220910174409227694895368145250528006099989456387123) * 10 ^ 70 +
        1503252353548519431105814906311483268589099144829350421933955727950834) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 251 = 136 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_250_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_251_prefix_zero :
    (∑ x ∈ Finset.range 137,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (251 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (251 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_251 :
    recurrence2Scalar1Left.coeff 251 =
      ((((1097 * 10 ^ 70 +
        5418332989953185771135718985557285521544312004672030735484205054723763) * 10 ^ 70 +
        4224333969950250764621434010207314735113433478041030205661158828769223) * 10 ^ 70 +
        4937445204976546311631440957250878165055117548596653475503186920645870) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 252 = 137 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_251_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_252_prefix_zero :
    (∑ x ∈ Finset.range 138,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (252 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (252 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_252 :
    recurrence2Scalar1Left.coeff 252 =
      -((((859 * 10 ^ 70 +
        8943747572156194065263613233649633429031852967780140634504060943819491) * 10 ^ 70 +
        8293038931523526376616481135034837681119046468167675283589588042121785) * 10 ^ 70 +
        3959094156127032891070474222006509159252558593684120698746995336277974) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 253 = 138 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_252_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_253_prefix_zero :
    (∑ x ∈ Finset.range 139,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (253 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (253 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_253 :
    recurrence2Scalar1Left.coeff 253 =
      ((((638 * 10 ^ 70 +
        9672931125619179150009322595305538921530825242692339449280507513167699) * 10 ^ 70 +
        1069233143304254577575849587730549945779460618222841675019230445729428) * 10 ^ 70 +
        4822884832102978941651407047538667695725810087897313314382057553714034) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 254 = 139 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_253_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_254_prefix_zero :
    (∑ x ∈ Finset.range 140,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (254 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (254 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_254 :
    recurrence2Scalar1Left.coeff 254 =
      -((((450 * 10 ^ 70 +
        4202416430073843744961413483168826219562843968710868719371455578120716) * 10 ^ 70 +
        6353383285980304183430610377932765998064189726775605718199648719180852) * 10 ^ 70 +
        2382751374601051303707342938581632276785609416317764063183445511882904) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 255 = 140 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_254_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_255_prefix_zero :
    (∑ x ∈ Finset.range 141,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (255 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (255 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_255 :
    recurrence2Scalar1Left.coeff 255 =
      ((((300 * 10 ^ 70 +
        7292446156662148414391495205289515236851246044017387529702352618293720) * 10 ^ 70 +
        7766738379493234387102748347158511187218641343524905730287710109970421) * 10 ^ 70 +
        9663433921646354556039800173772735721728886452796544628118664259760242) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 256 = 141 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_255_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_256_prefix_zero :
    (∑ x ∈ Finset.range 142,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (256 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (256 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_256 :
    recurrence2Scalar1Left.coeff 256 =
      -((((189 * 10 ^ 70 +
        4594933966617068994542962809233725550863948065950762165484613839039143) * 10 ^ 70 +
        7516692330164977208823277395488826991409784793482738696404018849387118) * 10 ^ 70 +
        0014666152170208823535831928175810308199189427784088905084542544746775) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 257 = 142 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_256_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_257_prefix_zero :
    (∑ x ∈ Finset.range 143,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (257 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (257 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_257 :
    recurrence2Scalar1Left.coeff 257 =
      ((((111 * 10 ^ 70 +
        8387427674502548004791989943388584445965049581768959428081314706527097) * 10 ^ 70 +
        3647621494391842239686139089520339898539713904243160641376772629496394) * 10 ^ 70 +
        2720665811995157112647234620375264101752522959337947701481562051838845) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 258 = 143 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_257_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_258_prefix_zero :
    (∑ x ∈ Finset.range 144,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (258 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (258 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_258 :
    recurrence2Scalar1Left.coeff 258 =
      -((((61 * 10 ^ 70 +
        0719834480644467086252073477822533456551673926038184340000521611465890) * 10 ^ 70 +
        1382311295401795321267677891523088766602131830566769034618495017800829) * 10 ^ 70 +
        0791431934925821194851957647952590629326701220018518586810431911645056) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 259 = 144 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_258_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_259_prefix_zero :
    (∑ x ∈ Finset.range 145,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (259 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (259 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_259 :
    recurrence2Scalar1Left.coeff 259 =
      ((((30 * 10 ^ 70 +
        0847662712237501416815834800662379323921932082632358488355152653991915) * 10 ^ 70 +
        0776771405860163147425359573851978774866485834151837917679074077345036) * 10 ^ 70 +
        2165914424496693249588261071764435356847814267739706756158874212197005) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 260 = 145 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_259_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_260_prefix_zero :
    (∑ x ∈ Finset.range 146,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (260 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (260 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_260 :
    recurrence2Scalar1Left.coeff 260 =
      -((((12 * 10 ^ 70 +
        6092616600547973416352182281572099817128119911988650077150749031444933) * 10 ^ 70 +
        7911493360179255818364690851180254163138549536201634704802284857606493) * 10 ^ 70 +
        6341335829417278572664041186286901424764950423078431140762669435792684) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 261 = 146 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_260_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_261_prefix_zero :
    (∑ x ∈ Finset.range 147,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (261 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (261 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_261 :
    recurrence2Scalar1Left.coeff 261 =
      ((((3 * 10 ^ 70 +
        6879495031668399096757960344690221519413750640085440568143864139446050) * 10 ^ 70 +
        1419732044904425250851766375002451773168455764250362678214901247360013) * 10 ^ 70 +
        6743728345056188993787879120611695235881502161580829436418801653253095) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 262 = 147 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_261_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_262_prefix_zero :
    (∑ x ∈ Finset.range 148,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (262 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (262 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_262 :
    recurrence2Scalar1Left.coeff 262 =
      (((2478710433128340043155950681408500356287770169517978222805485407249652 * 10 ^ 70 +
        9039647921092957080725661537526313829497725919877147590080898886557737) * 10 ^ 70 +
        8632275979435833128160426614004252951301221631381348656539328116366334) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 263 = 148 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_262_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_263_prefix_zero :
    (∑ x ∈ Finset.range 149,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (263 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (263 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_263 :
    recurrence2Scalar1Left.coeff 263 =
      -((((1 * 10 ^ 70 +
        5519625997817215318626803069680089883260145893202369189716286761053902) * 10 ^ 70 +
        9659945492983908445995209859250419469239424395545149321197856965879069) * 10 ^ 70 +
        0349450278089356164730077865738894223063191685460252814838635257338640) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 264 = 149 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_263_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_264_prefix_zero :
    (∑ x ∈ Finset.range 150,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (264 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (264 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_264 :
    recurrence2Scalar1Left.coeff 264 =
      ((((1 * 10 ^ 70 +
        6440155804614089583879435833201156049495338071775734082180433058681645) * 10 ^ 70 +
        2951035539616493064873531322434736419836880791966033597290233572193000) * 10 ^ 70 +
        1772445641914477628262136016896216150685041111532962834528107509998638) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 265 = 150 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_264_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_265_prefix_zero :
    (∑ x ∈ Finset.range 151,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (265 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (265 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_265 :
    recurrence2Scalar1Left.coeff 265 =
      -((((1 * 10 ^ 70 +
        2979157741361611886742071983203247109727004543576632977400467656867026) * 10 ^ 70 +
        2752796533683642232439637623861468678332323549247526337839666228554879) * 10 ^ 70 +
        4548335305395564505416811820771824831320418501883162016796040303063656) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 266 = 151 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_265_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_266_prefix_zero :
    (∑ x ∈ Finset.range 152,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (266 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (266 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_266 :
    recurrence2Scalar1Left.coeff 266 =
      (((8835381455406739903132285925487919161237530117094702174700058855380774 * 10 ^ 70 +
        4487843474909870741756311378196936433782866079655051035904945991176249) * 10 ^ 70 +
        2787721577498536892177987522883228483028049064664768416428167517214110) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 267 = 152 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_266_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_267_prefix_zero :
    (∑ x ∈ Finset.range 153,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (267 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (267 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_267 :
    recurrence2Scalar1Left.coeff 267 =
      -(((5435019470086859697924579686403042153148828339718732635517597070004291 * 10 ^ 70 +
        8736637925230442476349270662185484100218906334605295424705438586429639) * 10 ^ 70 +
        8097873202385680981226998193459970399978239966583521762261882770849889) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 268 = 153 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_267_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_268_prefix_zero :
    (∑ x ∈ Finset.range 154,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (268 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (268 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_268 :
    recurrence2Scalar1Left.coeff 268 =
      (((3082065026992658807629127581151635250121272225628196381677925629106423 * 10 ^ 70 +
        2475824227834833126588951665792038687291172349194457370883001763167180) * 10 ^ 70 +
        1437030209372052349975452731376895427146510419870293695709358406380770) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 269 = 154 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 19 +
      0 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_268_prefix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_269_prefix_zero :
    (∑ x ∈ Finset.range 155,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (269 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (269 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_269_suffix_zero :
    (∑ x ∈ Finset.range 1,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (269 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_269 :
    recurrence2Scalar1Left.coeff 269 =
      -(((1625838700867706413624784124382574414109081782782683078915427436020166 * 10 ^ 70 +
        6333351108959295370217021708007177569256013443729479091265150848848955) * 10 ^ 70 +
        1186043281788949618440988384681044449014965878514117540551570224546451) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 270 = 155 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 18 +
      1 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_269_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_269_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_270_prefix_zero :
    (∑ x ∈ Finset.range 156,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (270 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (270 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_270_suffix_zero :
    (∑ x ∈ Finset.range 2,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (270 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_270 :
    recurrence2Scalar1Left.coeff 270 =
      (((800350822543625409336209441698269432977026031224480136215285499448243 * 10 ^ 70 +
        1842300180810549443277903134924432230941705621914696251618950825519305) * 10 ^ 70 +
        3199471418300678238685093954390592913395092787051236543274472841040261) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 271 = 156 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 17 +
      2 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_270_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_270_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_271_prefix_zero :
    (∑ x ∈ Finset.range 157,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (271 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (271 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_271_suffix_zero :
    (∑ x ∈ Finset.range 3,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (271 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_271 :
    recurrence2Scalar1Left.coeff 271 =
      -(((367229220016802072578494042652869533920163216783039565621731960668970 * 10 ^ 70 +
        2836088853775229836412677895484193930341716645230763130931085134109479) * 10 ^ 70 +
        7246899367427257376714700271972415785877862749276072434910705366266314) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 272 = 157 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 16 +
      3 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_271_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_271_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_272_prefix_zero :
    (∑ x ∈ Finset.range 158,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (272 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (272 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_272_suffix_zero :
    (∑ x ∈ Finset.range 4,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (272 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_272 :
    recurrence2Scalar1Left.coeff 272 =
      (((156146855280538911276324665320504448690159201964216598940760290201617 * 10 ^ 70 +
        1721280570498632212860920325262798440179590146721091356520739775164053) * 10 ^ 70 +
        0890374467855508762769821007068546313997541357102990161302461919315426) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 273 = 158 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 15 +
      4 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_272_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_272_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_273_prefix_zero :
    (∑ x ∈ Finset.range 159,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (273 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (273 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_273_suffix_zero :
    (∑ x ∈ Finset.range 5,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (273 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_273 :
    recurrence2Scalar1Left.coeff 273 =
      -(((60749384200820798609431327315998323042943877885565354139137794395429 * 10 ^ 70 +
        1064538580702300018242052460779100341706559687152508346005361012641872) * 10 ^ 70 +
        9967351630064969253807306942541127930904145559610453347029176134190753) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 274 = 159 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 14 +
      5 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_273_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_273_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_274_prefix_zero :
    (∑ x ∈ Finset.range 160,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (274 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (274 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_274_suffix_zero :
    (∑ x ∈ Finset.range 6,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (274 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_274 :
    recurrence2Scalar1Left.coeff 274 =
      (((21055517629568190952699267792651781848915790188399982282409959748750 * 10 ^ 70 +
        0475089836201608082209637800593347577475663819733780149728045723526641) * 10 ^ 70 +
        2577363889795556882222684272597949382354534378767366797687149481879325) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 275 = 160 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 13 +
      6 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_274_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_274_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_275_prefix_zero :
    (∑ x ∈ Finset.range 161,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (275 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (275 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_275_suffix_zero :
    (∑ x ∈ Finset.range 7,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (275 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_275 :
    recurrence2Scalar1Left.coeff 275 =
      -(((6094144413796805878799801645075398716530762957957187722289410249564 * 10 ^ 70 +
        8600671964501807169763697782552831203046447471787476622332999340159294) * 10 ^ 70 +
        1921902415404197666827773019034383971471538201797881146883253363892538) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 276 = 161 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 12 +
      7 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_275_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_275_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_276_prefix_zero :
    (∑ x ∈ Finset.range 162,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (276 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (276 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_276_suffix_zero :
    (∑ x ∈ Finset.range 8,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (276 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_276 :
    recurrence2Scalar1Left.coeff 276 =
      (((1165836880865001513293617551871954061383438086982592636163015250568 * 10 ^ 70 +
        2496454647384411910387853008354946479630648008984292874660292170389190) * 10 ^ 70 +
        8530966533609078654378822260737938727860502834661535664336446406706038) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 277 = 162 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 11 +
      8 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_276_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_276_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_277_prefix_zero :
    (∑ x ∈ Finset.range 163,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (277 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (277 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_277_suffix_zero :
    (∑ x ∈ Finset.range 9,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (277 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_277 :
    recurrence2Scalar1Left.coeff 277 =
      (((121544299068746842267414002476465437733591245358090991551151412304 * 10 ^ 70 +
        5109160732124460119871100459479757820254412087850677616251661684229396) * 10 ^ 70 +
        4456243132565516333616657497293264319083911310364638634609702654582729) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 278 = 163 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 10 +
      9 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_277_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_277_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_278_prefix_zero :
    (∑ x ∈ Finset.range 164,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (278 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (278 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_278_suffix_zero :
    (∑ x ∈ Finset.range 10,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (278 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_278 :
    recurrence2Scalar1Left.coeff 278 =
      -(((284574299530861078886686208081027859560970181398673861875894417807 * 10 ^ 70 +
        0942582729342548081779290439849460447539519708598194257438089698012652) * 10 ^ 70 +
        8804429750464772736323088932819435245050830028290115687110279209806553) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 279 = 164 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 9 +
      10 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_278_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_278_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_279_prefix_zero :
    (∑ x ∈ Finset.range 165,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (279 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (279 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_279_suffix_zero :
    (∑ x ∈ Finset.range 11,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (279 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_279 :
    recurrence2Scalar1Left.coeff 279 =
      (((195295372457606685079411151693524559920405203363324370989796536421 * 10 ^ 70 +
        7598690876371237925822959765126267658322245675846026674017268295425131) * 10 ^ 70 +
        3326302165917122179397458976308670609084365167758318429098325468847202) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 280 = 165 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 8 +
      11 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_279_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_279_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_280_prefix_zero :
    (∑ x ∈ Finset.range 166,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (280 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (280 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_280_suffix_zero :
    (∑ x ∈ Finset.range 12,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (280 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_280 :
    recurrence2Scalar1Left.coeff 280 =
      -(((100982167587682916015998586375170859322484936537304320516466703727 * 10 ^ 70 +
        3403271100618238143369389344051805924048723278153816896745563139724879) * 10 ^ 70 +
        7604229452586044094999539328090662436874882952827114595050197841967826) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 281 = 166 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 7 +
      12 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_280_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_280_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_281_prefix_zero :
    (∑ x ∈ Finset.range 167,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (281 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (281 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_281_suffix_zero :
    (∑ x ∈ Finset.range 13,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (281 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_281 :
    recurrence2Scalar1Left.coeff 281 =
      (((44517022541602015104202659036063767558976966861665882582467276120 * 10 ^ 70 +
        4341390025560278917290367501305892076699750190662237847760853650984762) * 10 ^ 70 +
        9773222267977808026307789984046267765451204235224718285629723250435857) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 282 = 167 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 6 +
      13 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_281_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_281_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_282_prefix_zero :
    (∑ x ∈ Finset.range 168,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (282 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (282 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_282_suffix_zero :
    (∑ x ∈ Finset.range 14,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (282 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_282 :
    recurrence2Scalar1Left.coeff 282 =
      -(((17365366924748419294820806551176528388749491027712527542168240415 * 10 ^ 70 +
        8865170387072461164846652607563934870473878396902065507567593082093687) * 10 ^ 70 +
        0535719870784663189496475224042370536815507090069005870445991179982542) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 283 = 168 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 5 +
      14 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_282_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_282_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_283_prefix_zero :
    (∑ x ∈ Finset.range 169,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (283 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (283 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_283_suffix_zero :
    (∑ x ∈ Finset.range 15,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (283 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_283 :
    recurrence2Scalar1Left.coeff 283 =
      (((6050096431335251644153674519749048550733291654688622945901014035 * 10 ^ 70 +
        8212121701107258648738260973510981034929643524683596853672134833603538) * 10 ^ 70 +
        9914040301473014223944740653506174265107429872918487867417782976708599) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 284 = 169 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 4 +
      15 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_283_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_283_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_284_prefix_zero :
    (∑ x ∈ Finset.range 170,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (284 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (284 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_284_suffix_zero :
    (∑ x ∈ Finset.range 16,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (284 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_284 :
    recurrence2Scalar1Left.coeff 284 =
      -(((1866800344328814394350698886943052844513386050403472658597833611 * 10 ^ 70 +
        3109012576806640076269306438705724372564349706665242353718494455271007) * 10 ^ 70 +
        6126011049167763297953913179480077357555994583092127600201808381046171) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 285 = 170 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 3 +
      16 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_284_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_284_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_285_prefix_zero :
    (∑ x ∈ Finset.range 171,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (285 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (285 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_285_suffix_zero :
    (∑ x ∈ Finset.range 17,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (285 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_285 :
    recurrence2Scalar1Left.coeff 285 =
      (((493551809768574292313670662765715791329444477677754605572893090 * 10 ^ 70 +
        2563389364353323036265952044938552678806330225524870338177090209657285) * 10 ^ 70 +
        8784219178549367050764816742196542210211432841697234587446615337561054) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 286 = 171 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 2 +
      17 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_285_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_285_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_286_prefix_zero :
    (∑ x ∈ Finset.range 172,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (286 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (286 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_286_suffix_zero :
    (∑ x ∈ Finset.range 18,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (286 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_286 :
    recurrence2Scalar1Left.coeff 286 =
      -(((101047753475421628158672885055993073752704684980817028857140366 * 10 ^ 70 +
        5500953642112004386078794253548665437682414391985089888185548290913509) * 10 ^ 70 +
        0337678845983199700166154036043842720356387349822540138018788703189197) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 287 = 172 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 19 = 1 +
      18 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_286_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_286_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_287_prefix_zero :
    (∑ x ∈ Finset.range 173,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (287 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (287 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_287_suffix_zero :
    (∑ x ∈ Finset.range 19,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (287 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_287 :
    recurrence2Scalar1Left.coeff 287 =
      (((9138224297033329258716902775199048262964888222348302901581791 * 10 ^ 70 +
        2224117565462249203258249959925032486985061824666300962687494522492031) * 10 ^ 70 +
        2254295276396385097047318260980431548257799540865247490903843530787099) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 288 = 173 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 32 +
      19 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_287_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_287_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_288_prefix_zero :
    (∑ x ∈ Finset.range 174,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (288 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (288 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_288_suffix_zero :
    (∑ x ∈ Finset.range 20,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (288 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_288 :
    recurrence2Scalar1Left.coeff 288 =
      (((4840621586437811488852919244520877961933454960730966616591537 * 10 ^ 70 +
        1968892108930800934909483946630452182223930867458817455052033384317002) * 10 ^ 70 +
        7238153255165674041108270502212785927677064751026401778721879843767410) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 289 = 174 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 31 +
      20 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_288_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_288_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_289_prefix_zero :
    (∑ x ∈ Finset.range 175,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (289 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (289 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_289_suffix_zero :
    (∑ x ∈ Finset.range 21,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (289 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_289 :
    recurrence2Scalar1Left.coeff 289 =
      -(((3695647168258096054525608997002435648054875381453816593648262 * 10 ^ 70 +
        7757537767956827836228602352793943895715320584108347521855211460141606) * 10 ^ 70 +
        8553916776567103825089616306241608016134298997741786002365667397671381) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 290 = 175 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 30 +
      21 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_289_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_289_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_290_prefix_zero :
    (∑ x ∈ Finset.range 176,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (290 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (290 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_290_suffix_zero :
    (∑ x ∈ Finset.range 22,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (290 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_290 :
    recurrence2Scalar1Left.coeff 290 =
      (((1639842703302018965024805120735933355885698191574083156772586 * 10 ^ 70 +
        6724115602254570038204047215512646744615374257008048246784131346619521) * 10 ^ 70 +
        7590650678480884734742179686461517604555623444039888511315962980424195) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 291 = 176 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 29 +
      22 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_290_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_290_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_291_prefix_zero :
    (∑ x ∈ Finset.range 177,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (291 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (291 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_291_suffix_zero :
    (∑ x ∈ Finset.range 23,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (291 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_291 :
    recurrence2Scalar1Left.coeff 291 =
      -(((575777939635962422280987617703292202753179874784826149396464 * 10 ^ 70 +
        0090275007422439875482048763933543650171511875162508456043529123894876) * 10 ^ 70 +
        4573371620103536460817977593047609486796285417597607228040251507387373) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 292 = 177 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 28 +
      23 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_291_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_291_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_292_prefix_zero :
    (∑ x ∈ Finset.range 178,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (292 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (292 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_292_suffix_zero :
    (∑ x ∈ Finset.range 24,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (292 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_292 :
    recurrence2Scalar1Left.coeff 292 =
      (((170278106061509030605728471545884782879730837263296639047000 * 10 ^ 70 +
        2207286775779882111956491269241684451408138123495152766098309147192594) * 10 ^ 70 +
        6103458231346223763656262337659963714559662182041121637259904684350153) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 293 = 178 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 27 +
      24 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_292_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_292_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_293_prefix_zero :
    (∑ x ∈ Finset.range 179,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (293 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (293 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_293_suffix_zero :
    (∑ x ∈ Finset.range 25,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (293 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_293 :
    recurrence2Scalar1Left.coeff 293 =
      -(((42536933925813190154153503647042851955069115442332366832008 * 10 ^ 70 +
        5201155251488046597698584719808033260265660684407644193669153705093386) * 10 ^ 70 +
        7400694824914488622345267996279742692048253886623075163807750695252242) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 294 = 179 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 26 +
      25 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_293_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_293_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_294_prefix_zero :
    (∑ x ∈ Finset.range 180,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (294 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (294 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_294_suffix_zero :
    (∑ x ∈ Finset.range 26,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (294 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_294 :
    recurrence2Scalar1Left.coeff 294 =
      (((8547255569011395160375176556697406932122609822960184917669 * 10 ^ 70 +
        8709634069865947793050975209164411347734130790159492342646058150914339) * 10 ^ 70 +
        3427141585064952743479146663690509551760736301237217057972067364315035) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 295 = 180 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 25 +
      26 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_294_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_294_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_295_prefix_zero :
    (∑ x ∈ Finset.range 181,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (295 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (295 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_295_suffix_zero :
    (∑ x ∈ Finset.range 27,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (295 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_295 :
    recurrence2Scalar1Left.coeff 295 =
      -(((1116670723557411746223029112756740310523245729005691338576 * 10 ^ 70 +
        4129391326675228677143687846380308622613628100966879697319876841446997) * 10 ^ 70 +
        9795407946447300260271415867152570394816289112852053486258346811629001) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 296 = 181 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 24 +
      27 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_295_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_295_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_296_prefix_zero :
    (∑ x ∈ Finset.range 182,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (296 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (296 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_296_suffix_zero :
    (∑ x ∈ Finset.range 28,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (296 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_296 :
    recurrence2Scalar1Left.coeff 296 =
      -(((57346061397437972357519173931352793710297942299134405910 * 10 ^ 70 +
        7335466087029298099793225665163559307679853900499585008315381261129074) * 10 ^ 70 +
        2325722056673912526456593835761331602980142424085891970204497043614178) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 297 = 182 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 23 +
      28 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_296_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_296_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_297_prefix_zero :
    (∑ x ∈ Finset.range 183,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (297 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (297 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_297_suffix_zero :
    (∑ x ∈ Finset.range 29,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (297 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_297 :
    recurrence2Scalar1Left.coeff 297 =
      (((100335536818710936982120972167691196318478802573547538043 * 10 ^ 70 +
        2718778939931598436692128670307699891153411813220630747020076682587970) * 10 ^ 70 +
        8869902473094196423110943628621517992966394979025180148399561300686524) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 298 = 183 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 22 +
      29 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_297_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_297_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_298_prefix_zero :
    (∑ x ∈ Finset.range 184,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (298 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (298 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_298_suffix_zero :
    (∑ x ∈ Finset.range 30,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (298 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_298 :
    recurrence2Scalar1Left.coeff 298 =
      -(((41731294986354804459782994994619833827156437878890368146 * 10 ^ 70 +
        1973518903926542672431780610754864066371429478747909428099552046371471) * 10 ^ 70 +
        1940354719188576781885562581563173182436729913760724058799817878861832) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 299 = 184 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 21 +
      30 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_298_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_298_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_299_prefix_zero :
    (∑ x ∈ Finset.range 185,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (299 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (299 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_299_suffix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (299 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_299 :
    recurrence2Scalar1Left.coeff 299 =
      (((12296672402587081317962604475461544545397292227497871873 * 10 ^ 70 +
        0642134431484620195975559622395904344135750383078002419513312247916834) * 10 ^ 70 +
        8781957015233609525152019649033392706936988506597155157268765392657462) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 300 = 185 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 20 +
      31 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_299_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_299_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_300_prefix_zero :
    (∑ x ∈ Finset.range 186,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (300 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (300 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_300_suffix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (300 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_300 :
    recurrence2Scalar1Left.coeff 300 =
      -(((2849262658949844923188744913756131818787811052553961714 * 10 ^ 70 +
        0760366221475146724834971551903033875216139269272436357263624902426171) * 10 ^ 70 +
        1975011546952965613634618028764204369962197515665891442207558287418967) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 301 = 186 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 19 +
      32 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_300_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_300_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_301_prefix_zero :
    (∑ x ∈ Finset.range 187,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (301 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (301 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_301_suffix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (301 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_301 :
    recurrence2Scalar1Left.coeff 301 =
      (((503878432383144652859784802042196423807690671024216228 * 10 ^ 70 +
        5852021464441120445375472694151040239958705532795133653285098120166104) * 10 ^ 70 +
        5404769039557794901340067562297834558800624430567614773409823702979478) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 302 = 187 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 18 +
      33 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_301_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_301_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_302_prefix_zero :
    (∑ x ∈ Finset.range 188,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (302 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (302 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_302_suffix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (302 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_302 :
    recurrence2Scalar1Left.coeff 302 =
      -(((51636171412378848378233127251526425694089147406226764 * 10 ^ 70 +
        9139675155071533486210261034502121631057074326131149721341332984448393) * 10 ^ 70 +
        0104512917658395826896099704867945436228943979433749488701350188345470) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 303 = 188 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 17 +
      34 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_302_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_302_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_303_prefix_zero :
    (∑ x ∈ Finset.range 189,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (303 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (303 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_303_suffix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (303 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_303 :
    recurrence2Scalar1Left.coeff 303 =
      -(((5984983092154620320400095622173454888187897622155843 * 10 ^ 70 +
        3989199740342495796824089974547763402578522944693623468622342810217560) * 10 ^ 70 +
        7330222088962003750071912802612146985759488725720976395913010565122681) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 304 = 189 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 16 +
      35 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_303_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_303_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_304_prefix_zero :
    (∑ x ∈ Finset.range 190,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (304 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (304 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_304_suffix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (304 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_304 :
    recurrence2Scalar1Left.coeff 304 =
      (((5111161000820839736465909427883080938607750409601306 * 10 ^ 70 +
        0423031268774651322690761821830873650206946319348490331221926195901151) * 10 ^ 70 +
        8375354949782978709222729204675304308715128674097692607466889234367639) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 305 = 190 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 15 +
      36 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_304_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_304_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_305_prefix_zero :
    (∑ x ∈ Finset.range 191,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (305 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (305 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_305_suffix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (305 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_305 :
    recurrence2Scalar1Left.coeff 305 =
      -(((1730634444651650483716661532653303383111576206836360 * 10 ^ 70 +
        8046024249901494594952971154024050294136725409555909369268211544952661) * 10 ^ 70 +
        2848048496745583565090905063134453742141557322051903155808607482603198) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 306 = 191 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 14 +
      37 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_305_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_305_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_306_prefix_zero :
    (∑ x ∈ Finset.range 192,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (306 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (306 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_306_suffix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (306 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_306 :
    recurrence2Scalar1Left.coeff 306 =
      (((429699300398752270133578731083145366975836063752356 * 10 ^ 70 +
        8758309891133314629297694052695753437743458319080081385889785840457477) * 10 ^ 70 +
        2899688119590769543862955099860241756499597947470732549007673202996742) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 307 = 192 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 13 +
      38 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_306_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_306_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_307_prefix_zero :
    (∑ x ∈ Finset.range 193,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (307 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (307 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_307_suffix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (307 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_307 :
    recurrence2Scalar1Left.coeff 307 =
      -(((85195423916756505450683751977097265670210221725149 * 10 ^ 70 +
        4673758162544809364380294879294460040633010439682443804736133508034962) * 10 ^ 70 +
        0184121621545184549966406519020513445522615646895103872575464265398975) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 308 = 193 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 12 +
      39 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_307_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_307_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_308_prefix_zero :
    (∑ x ∈ Finset.range 194,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (308 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (308 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_308_suffix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (308 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_308 :
    recurrence2Scalar1Left.coeff 308 =
      (((13295655647213254899340673025496370872912266688052 * 10 ^ 70 +
        7756706365812485323213797863542627133381091386150661305277861743371629) * 10 ^ 70 +
        8293712551757666302703492687899797141716356646151629317577662769955505) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 309 = 194 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 11 +
      40 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_308_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_308_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_309_prefix_zero :
    (∑ x ∈ Finset.range 195,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (309 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (309 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_309_suffix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (309 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_309 :
    recurrence2Scalar1Left.coeff 309 =
      -(((1403883081392215074423335413667446851759425232068 * 10 ^ 70 +
        7924271924039760123852537919121014288616540732707059876344422799324386) * 10 ^ 70 +
        6138430480987916423388931299114332949850272888432011014628352283855675) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 310 = 195 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 10 +
      41 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_309_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_309_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_310_prefix_zero :
    (∑ x ∈ Finset.range 196,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (310 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (310 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_310_suffix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (310 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_310 :
    recurrence2Scalar1Left.coeff 310 =
      (((2181375926579611737923080073711644955820444900 * 10 ^ 70 +
        0082707354198765705466969079962003883764692186620801547822049519586257) * 10 ^ 70 +
        3973827565823232864199281383184617382044563874176624761312331235172271) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 311 = 196 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 9 +
      42 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_310_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_310_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_311_prefix_zero :
    (∑ x ∈ Finset.range 197,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (311 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (311 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_311_suffix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (311 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_311 :
    recurrence2Scalar1Left.coeff 311 =
      (((45417688667268203283209021291820520962324804009 * 10 ^ 70 +
        6977147212368288560403253327151007525653255987266912417494814661779578) * 10 ^ 70 +
        0470286819881845873027389892713739887185752508952316612446860052659791) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 312 = 197 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 8 +
      43 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_311_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_311_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_312_prefix_zero :
    (∑ x ∈ Finset.range 198,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (312 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (312 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_312_suffix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (312 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_312 :
    recurrence2Scalar1Left.coeff 312 =
      -(((14208114080832221160983361665418818892813497507 * 10 ^ 70 +
        2813072461714499737990867806025529689827612372003972745567120916518703) * 10 ^ 70 +
        5893949335975633300434594969003308199416801807214880100342209539290830) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 313 = 198 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 7 +
      44 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_312_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_312_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_313_prefix_zero :
    (∑ x ∈ Finset.range 199,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (313 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (313 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_313_suffix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (313 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_313 :
    recurrence2Scalar1Left.coeff 313 =
      (((2966283225460584667622662915687696828887125592 * 10 ^ 70 +
        6486310807837075562144901883299625142164594402099809025038425030018549) * 10 ^ 70 +
        1296421518842817845830144080505336014433951188932083818328120515297834) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 314 = 199 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 6 +
      45 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_313_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_313_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_314_prefix_zero :
    (∑ x ∈ Finset.range 200,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (314 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (314 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_314_suffix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (314 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_314 :
    recurrence2Scalar1Left.coeff 314 =
      -(((479909381594723487337760038571741784907665762 * 10 ^ 70 +
        6494433386628336851711875685797035417345034318607039224880840181615684) * 10 ^ 70 +
        3631224993342580105567371851365117398834218289788339197101892820824673) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 315 = 200 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 5 +
      46 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_314_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_314_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_315_prefix_zero :
    (∑ x ∈ Finset.range 201,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (315 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (315 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_315_suffix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (315 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_315 :
    recurrence2Scalar1Left.coeff 315 =
      (((60418289174267968743098824628090000504793700 * 10 ^ 70 +
        4108605459731165961710747180364640105087431331142066254911852021318810) * 10 ^ 70 +
        9550728028389342708375298150966707636776996239842455709152715848748795) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 316 = 201 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 4 +
      47 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_315_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_315_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_316_prefix_zero :
    (∑ x ∈ Finset.range 202,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (316 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (316 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_316_suffix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (316 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_316 :
    recurrence2Scalar1Left.coeff 316 =
      -(((5242715742692346389098955520176955126352619 * 10 ^ 70 +
        4940668881429990441360500799881442771442987643571270761545942098539473) * 10 ^ 70 +
        1576998145553132687573361526810982048933160737311886242317448931227702) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 317 = 202 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 3 +
      48 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_316_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_316_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_317_prefix_zero :
    (∑ x ∈ Finset.range 203,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (317 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (317 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_317_suffix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (317 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_317 :
    recurrence2Scalar1Left.coeff 317 =
      (((88049063464243171670400178811065430674198 * 10 ^ 70 +
        0121025805713843591392892071292583943640933043323935034337577822454848) * 10 ^ 70 +
        7071173854220546921027835791538884247057923247485336386669566790696097) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 318 = 203 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 2 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_317_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_317_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_318_prefix_zero :
    (∑ x ∈ Finset.range 204,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (318 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (318 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_318_suffix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (318 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_318 :
    recurrence2Scalar1Left.coeff 318 =
      (((75887367200558646107724149004539785353870 * 10 ^ 70 +
        8832134551664944569019593063614702847765498215166514505382265865147631) * 10 ^ 70 +
        1896124847077336667506939475679674471614667743247105505675409132735799) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 319 = 204 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 51 = 1 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_318_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_318_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_319_prefix_zero :
    (∑ x ∈ Finset.range 205,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (319 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (319 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_319_suffix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (319 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_319 :
    recurrence2Scalar1Left.coeff 319 =
      -(((18561255386397169767684534726764400149768 * 10 ^ 70 +
        6112629979789007584750556736418793758804236616567971229088067900380986) * 10 ^ 70 +
        6313315772631018498877982406992652714423333106904841216418248769366007) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 320 = 205 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 32 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_319_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_319_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_320_prefix_zero :
    (∑ x ∈ Finset.range 206,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (320 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (320 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_320_suffix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (320 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_320 :
    recurrence2Scalar1Left.coeff 320 =
      (((2788478904430205253962953246364919277295 * 10 ^ 70 +
        7528096448468090010317249346194439976172783780400931848974537390132231) * 10 ^ 70 +
        4826234503416831247145425488567128639560707748101929853739428373690995) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 321 = 206 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 31 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_320_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_320_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_321_prefix_zero :
    (∑ x ∈ Finset.range 207,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (321 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (321 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_321_suffix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (321 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_321 :
    recurrence2Scalar1Left.coeff 321 =
      -(((301025857159466237150692170130121741757 * 10 ^ 70 +
        1169904829747040816347936979359102565379388201773391390089710868646399) * 10 ^ 70 +
        4643471499758252166953527918255241483485780705463443292487110425205605) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 322 = 207 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 30 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_321_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_321_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_322_prefix_zero :
    (∑ x ∈ Finset.range 208,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (322 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (322 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_322_suffix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (322 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_322 :
    recurrence2Scalar1Left.coeff 322 =
      (((21343389216377343992143513608525501012 * 10 ^ 70 +
        1225142073756007150989227410573894763141805198802043689574968934125599) * 10 ^ 70 +
        4800888879842030751539413270468148143668575226582526659076110288527255) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 323 = 208 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 29 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_322_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_322_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_323_prefix_zero :
    (∑ x ∈ Finset.range 209,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (323 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (323 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_323_suffix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (323 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_323 :
    recurrence2Scalar1Left.coeff 323 =
      -(((242444772775672851361497271725228172 * 10 ^ 70 +
        7851156786260481278890378558165955574229946706199839451478934397504213) * 10 ^ 70 +
        1567497610771865856760399482904387077507313307595927850549407127894031) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 324 = 209 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 28 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_323_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_323_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_324_prefix_zero :
    (∑ x ∈ Finset.range 210,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (324 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (324 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_324_suffix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (324 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_324 :
    recurrence2Scalar1Left.coeff 324 =
      -(((201549288940403955781748121819388720 * 10 ^ 70 +
        9941143360407375246049772249831218211075072692196049670640989062727973) * 10 ^ 70 +
        6553494858806756621877146528182918529801764634571950147770276462158610) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 325 = 210 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 27 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_324_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_324_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_325_prefix_zero :
    (∑ x ∈ Finset.range 211,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (325 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (325 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_325_suffix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (325 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_325 :
    recurrence2Scalar1Left.coeff 325 =
      (((36831140048340710457956298645489621 * 10 ^ 70 +
        8229140379588926797306726896008218225158204071094707834486442240224235) * 10 ^ 70 +
        4192349583171462579270920652725957073764735741452687109182806301958212) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 326 = 211 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 26 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_325_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_325_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_326_prefix_zero :
    (∑ x ∈ Finset.range 212,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (326 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (326 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_326_suffix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (326 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_326 :
    recurrence2Scalar1Left.coeff 326 =
      -(((4021698553189127255617025909894725 * 10 ^ 70 +
        1849696994510995157926140664152772193239051230365323726223751621812241) * 10 ^ 70 +
        6108409534346760517440167167019037466768197595450625801917150490685570) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 327 = 212 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 25 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_326_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_326_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_327_prefix_zero :
    (∑ x ∈ Finset.range 213,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (327 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (327 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_327_suffix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (327 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_327 :
    recurrence2Scalar1Left.coeff 327 =
      (((295967637668269454377092270010277 * 10 ^ 70 +
        3921435569109586169376016425676909746846090281289344589625389219642239) * 10 ^ 70 +
        2027355083015872149409334063213353311936881299690289389954033834162635) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 328 = 213 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 24 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_327_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_327_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_328_prefix_zero :
    (∑ x ∈ Finset.range 214,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (328 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (328 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_328_suffix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (328 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_328 :
    recurrence2Scalar1Left.coeff 328 =
      -(((11318477819114571970574707288105 * 10 ^ 70 +
        1934855171445067599928351247709562823320365793884297470663569642152840) * 10 ^ 70 +
        8102909004953207035160076511755678142918092253926768493453641360160492) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 329 = 214 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 23 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_328_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_328_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_329_prefix_zero :
    (∑ x ∈ Finset.range 215,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (329 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (329 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_329_suffix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (329 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_329 :
    recurrence2Scalar1Left.coeff 329 =
      -(((537164163642700508652514352581 * 10 ^ 70 +
        3271470715903222784751366146147811476294630107143550127206526900181330) * 10 ^ 70 +
        2461984432522784312038233186952082521918065416977311118968117320090628) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 330 = 215 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 22 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_329_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_329_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_330_prefix_zero :
    (∑ x ∈ Finset.range 216,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (330 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (330 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_330_suffix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (330 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_330 :
    recurrence2Scalar1Left.coeff 330 =
      (((139722168821864021906582479364 * 10 ^ 70 +
        0603075663130471007400196118302225724848955330707819103431947755082972) * 10 ^ 70 +
        3298830716166321970244504005648986030219762295865159480359646859899730) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 331 = 216 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 21 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_330_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_330_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_331_prefix_zero :
    (∑ x ∈ Finset.range 217,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (331 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (331 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_331_suffix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (331 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_331 :
    recurrence2Scalar1Left.coeff 331 =
      -(((13759385893966293666698634764 * 10 ^ 70 +
        2184784527232770605166953372938365770749820838116389514381275264625916) * 10 ^ 70 +
        4699166544718273473929243376809987867030456558176470487978936299246594) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 332 = 217 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 20 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_331_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_331_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_332_prefix_zero :
    (∑ x ∈ Finset.range 218,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (332 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (332 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_332_suffix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (332 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_332 :
    recurrence2Scalar1Left.coeff 332 =
      (((854655067669397577496492026 * 10 ^ 70 +
        0663628342661150913800154333735302411784993483781528316288223098758512) * 10 ^ 70 +
        4347779517531224941150709909168171576909119225000705449545488956988676) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 333 = 218 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 19 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_332_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_332_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_333_prefix_zero :
    (∑ x ∈ Finset.range 219,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (333 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (333 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_333_suffix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (333 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_333 :
    recurrence2Scalar1Left.coeff 333 =
      -(((30029855634684375906395409 * 10 ^ 70 +
        6905292976477546833433234804409363620796978146141361933904246225007727) * 10 ^ 70 +
        0463181999192796746563047996958120237211882456826955184718499780771600) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 334 = 219 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 18 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_333_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_333_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_334_prefix_zero :
    (∑ x ∈ Finset.range 220,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (334 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (334 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_334_suffix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (334 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_334 :
    recurrence2Scalar1Left.coeff 334 =
      -(((261384235681867753988922 * 10 ^ 70 +
        9319155390020711211263059485549738757084659004137021441946624614056503) * 10 ^ 70 +
        3683772965791540617989960415191896015666023322236885277658515806009625) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 335 = 220 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 17 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_334_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_334_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_335_prefix_zero :
    (∑ x ∈ Finset.range 221,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (335 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (335 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_335_suffix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (335 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_335 :
    recurrence2Scalar1Left.coeff 335 =
      (((115978250359657019327444 * 10 ^ 70 +
        6439188686278150901927342916615817985956051485921303632440320054503049) * 10 ^ 70 +
        0715680787424347515685876325809066942429806497140033718842087506308183) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 336 = 221 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 16 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_335_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_335_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_336_prefix_zero :
    (∑ x ∈ Finset.range 222,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (336 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (336 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_336_suffix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (336 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_336 :
    recurrence2Scalar1Left.coeff 336 =
      -(((8437549490804282001416 * 10 ^ 70 +
        2460825502750900394960561162810719255428535160900977087588850942568218) * 10 ^ 70 +
        8634296513328659380865967833884250034581338187874938815182235293877781) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 337 = 222 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 15 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_336_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_336_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_337_prefix_zero :
    (∑ x ∈ Finset.range 223,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (337 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (337 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_337_suffix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (337 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_337 :
    recurrence2Scalar1Left.coeff 337 =
      (((342021673587839571693 * 10 ^ 70 +
        4846810325993576598707179252021480402874636356239115509450386260336038) * 10 ^ 70 +
        2400809136813554753615048023513993415671480064177975661937858310796145) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 338 = 223 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 14 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_337_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_337_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_338_prefix_zero :
    (∑ x ∈ Finset.range 224,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (338 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (338 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_338_suffix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (338 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_338 :
    recurrence2Scalar1Left.coeff 338 =
      -(((6151867453481513706 * 10 ^ 70 +
        5015626148256122339021537877433801345743507364591871687542117060425020) * 10 ^ 70 +
        3772258155080390076747298888671567911425932206401783086499723013610688) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 339 = 224 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 13 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_338_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_338_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_339_prefix_zero :
    (∑ x ∈ Finset.range 225,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (339 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (339 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_339_suffix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (339 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_339 :
    recurrence2Scalar1Left.coeff 339 =
      -(((176272250668543886 * 10 ^ 70 +
        7351112463717277521192177778138220195414417041416701000703803704763882) * 10 ^ 70 +
        5372060075266793481289917876050351556397779407229334521773554455209729) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 340 = 225 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 12 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_339_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_339_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_340_prefix_zero :
    (∑ x ∈ Finset.range 226,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (340 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (340 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_340_suffix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (340 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_340 :
    recurrence2Scalar1Left.coeff 340 =
      (((16636731183259529 * 10 ^ 70 +
        5637992731067890865583646091045866613139345402966222115992894217757408) * 10 ^ 70 +
        2935205236883227524238479686252169727475532016405486156136076041101135) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 341 = 226 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 11 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_340_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_340_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_341_prefix_zero :
    (∑ x ∈ Finset.range 227,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (341 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (341 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_341_suffix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (341 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_341 :
    recurrence2Scalar1Left.coeff 341 =
      -(((554376978962637 * 10 ^ 70 +
        2147321900749745656132027439025277239680668298677251824944121526494672) * 10 ^ 70 +
        9067845373350638453402386203243075939964428937419686074699640811077606) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 342 = 227 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 10 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_341_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_341_suffix_zero]
  norm_num [Finset.sum_range_succ]

private theorem recurrence2Scalar1Left_coeff_342_prefix_zero :
    (∑ x ∈ Finset.range 228,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (342 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (342 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

private theorem recurrence2Scalar1Left_coeff_342_suffix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff (269 + x) *
        remainder2Coefficient1.coeff (342 - (269 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2LeadingSquare_coeff_high (269 + x) (by omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_342 :
    recurrence2Scalar1Left.coeff 342 =
      (((7642252769921 * 10 ^ 70 +
        4919283076139372733921499105748215189511464949182661544647026474365647) * 10 ^ 70 +
        4994161817629929130301859068713412265279652145797662747514532074939223) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 343 = 228 +
    115 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 9 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence2Scalar1Left_coeff_342_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence2Scalar1Left_coeff_342_suffix_zero]
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

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
  norm_num [Finset.sum_range_succ]

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
