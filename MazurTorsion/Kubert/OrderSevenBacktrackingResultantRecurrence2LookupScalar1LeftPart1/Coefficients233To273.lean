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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

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
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
