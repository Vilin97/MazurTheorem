/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupLeadingSquare
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupA1
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence2LookupScalar1LeftPart0Simp
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

private theorem recurrence2Scalar1Left_coeff_145_prefix_zero :
    (∑ x ∈ Finset.range 31,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (145 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (145 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_145 :
    recurrence2Scalar1Left.coeff 145 =
      (((31820362652380089243468123162456601072 * 10 ^ 70 +
        1962957275696682424924907265743155401657304165790736867818173800289964) * 10 ^ 70 +
        5444691827183195792633063605155591843592102619463159560522862584272285) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 146 = 31 +
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
  rw [recurrence2Scalar1Left_coeff_145_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_146_prefix_zero :
    (∑ x ∈ Finset.range 32,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (146 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (146 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_146 :
    recurrence2Scalar1Left.coeff 146 =
      -(((235330746419562023688155495883195025596 * 10 ^ 70 +
        2986102147191078083390460803411400816976963994139352921266737680217682) * 10 ^ 70 +
        8344220618994903511276485369937285516411643800683468740365579151724791) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 147 = 32 +
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
  rw [recurrence2Scalar1Left_coeff_146_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_147_prefix_zero :
    (∑ x ∈ Finset.range 33,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (147 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (147 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_147 :
    recurrence2Scalar1Left.coeff 147 =
      (((383224190085423470424286790263888278744 * 10 ^ 70 +
        7779865555908358052690185708412418527130620173868228137811980829792439) * 10 ^ 70 +
        8530056638983647147054342630801344813785701175207218682463214131851731) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 148 = 33 +
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
  rw [recurrence2Scalar1Left_coeff_147_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_148_prefix_zero :
    (∑ x ∈ Finset.range 34,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (148 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (148 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_148 :
    recurrence2Scalar1Left.coeff 148 =
      (((1687459308805876336081443314082449112576 * 10 ^ 70 +
        3900898909911879685061471526706032309318814285216125084531155005324728) * 10 ^ 70 +
        7527572681596142797801797713470598639087290204891958908503732710030185) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 149 = 34 +
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
  rw [recurrence2Scalar1Left_coeff_148_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_149_prefix_zero :
    (∑ x ∈ Finset.range 35,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (149 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (149 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_149 :
    recurrence2Scalar1Left.coeff 149 =
      -(((10033975541588596032659981707968330613508 * 10 ^ 70 +
        0641759841002179023184646479808711757304606937779876669010295461086732) * 10 ^ 70 +
        5900077905805175965243277242065790577046437894240235481840191682565602) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 150 = 35 +
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
  rw [recurrence2Scalar1Left_coeff_149_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_150_prefix_zero :
    (∑ x ∈ Finset.range 36,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (150 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (150 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_150 :
    recurrence2Scalar1Left.coeff 150 =
      (((9756584650265180654801222517314861812702 * 10 ^ 70 +
        7120018603558154789647749768751842147833720094600406951222232222479777) * 10 ^ 70 +
        2989320453968277295442934481910703387942931070903129132404914147095989) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 151 = 36 +
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
  rw [recurrence2Scalar1Left_coeff_150_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_151_prefix_zero :
    (∑ x ∈ Finset.range 37,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (151 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (151 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_151 :
    recurrence2Scalar1Left.coeff 151 =
      (((98126030626529138286845642102770298235477 * 10 ^ 70 +
        8295038136803159376649247185826302587470031883447467291392046826505036) * 10 ^ 70 +
        3574289155593990990995244593104019799783044180839284172802221428791607) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 152 = 37 +
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
  rw [recurrence2Scalar1Left_coeff_151_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_152_prefix_zero :
    (∑ x ∈ Finset.range 38,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (152 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (152 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_152 :
    recurrence2Scalar1Left.coeff 152 =
      -(((429909733404163788992105087470623891746324 * 10 ^ 70 +
        1191583633475948792363097910320330251223272002584710002040187515519717) * 10 ^ 70 +
        0860008667124367529349320509033390606434265254895427011928941893782800) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 153 = 38 +
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
  rw [recurrence2Scalar1Left_coeff_152_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_153_prefix_zero :
    (∑ x ∈ Finset.range 39,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (153 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (153 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_153 :
    recurrence2Scalar1Left.coeff 153 =
      (((20316122568169086500118202241828860054782 * 10 ^ 70 +
        7573506556273966607836372177271256456191910480943680592359350843795863) * 10 ^ 70 +
        1238950764399437018573108865789038624321841332559703557814863101657835) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 154 = 39 +
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
  rw [recurrence2Scalar1Left_coeff_153_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_154_prefix_zero :
    (∑ x ∈ Finset.range 40,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (154 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (154 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_154 :
    recurrence2Scalar1Left.coeff 154 =
      (((6067462494969625532128302114397135893829169 * 10 ^ 70 +
        6722457276567641368456007672700463169252551955325824538959638877877538) * 10 ^ 70 +
        3561487122112230886032946701757091096301596997323525852944018135827851) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 155 = 40 +
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
  rw [recurrence2Scalar1Left_coeff_154_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_155_prefix_zero :
    (∑ x ∈ Finset.range 41,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (155 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (155 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_155 :
    recurrence2Scalar1Left.coeff 155 =
      -(((22288164145983650556192829863014886336599084 * 10 ^ 70 +
        0700830085341303062232914372512807292631497827253761247156266561979090) * 10 ^ 70 +
        3886444790899230600610990728669291088243553368567105904140863712522905) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 156 = 41 +
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
  rw [recurrence2Scalar1Left_coeff_155_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_156_prefix_zero :
    (∑ x ∈ Finset.range 42,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (156 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (156 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_156 :
    recurrence2Scalar1Left.coeff 156 =
      -(((1673573281707107958958050185341373720918107 * 10 ^ 70 +
        0569926917130006465187006889910835843833029859360602562101883928877593) * 10 ^ 70 +
        1521891898024487585268340642100360218651196751080820506386256297562590) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 157 = 42 +
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
  rw [recurrence2Scalar1Left_coeff_156_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_157_prefix_zero :
    (∑ x ∈ Finset.range 43,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (157 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (157 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_157 :
    recurrence2Scalar1Left.coeff 157 =
      (((313592723996693401090006227784180129932531424 * 10 ^ 70 +
        0771518363385479181111852807783316339362051243905578807763422306234559) * 10 ^ 70 +
        9250799785630654601369716979019690223281816946531495251511105631164882) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 158 = 43 +
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
  rw [recurrence2Scalar1Left_coeff_157_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_158_prefix_zero :
    (∑ x ∈ Finset.range 44,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (158 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (158 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_158 :
    recurrence2Scalar1Left.coeff 158 =
      -(((1205548280645098160003720143658148364377226563 * 10 ^ 70 +
        7310176812201661393343119089942303838696754900489093232776899581379181) * 10 ^ 70 +
        1074939399973672632906818230127808766875041056408696360402004650053036) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 159 = 44 +
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
  rw [recurrence2Scalar1Left_coeff_158_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_159_prefix_zero :
    (∑ x ∈ Finset.range 45,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (159 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (159 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_159 :
    recurrence2Scalar1Left.coeff 159 =
      (((686155695774553080981139102667191890699380015 * 10 ^ 70 +
        1467174349217026574976484386768821642488038440153246104690756738402365) * 10 ^ 70 +
        4645372047621395593605284772272486321604137244877628044831809750523974) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 160 = 45 +
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
  rw [recurrence2Scalar1Left_coeff_159_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_160_prefix_zero :
    (∑ x ∈ Finset.range 46,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (160 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (160 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_160 :
    recurrence2Scalar1Left.coeff 160 =
      (((12429064750314347853717149646214781249127719641 * 10 ^ 70 +
        8614088807439084023141545876272014971414200182405326956876231724074420) * 10 ^ 70 +
        4696231615550979162370350720989966142200928770998233726583335805404891) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 161 = 46 +
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
  rw [recurrence2Scalar1Left_coeff_160_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_161_prefix_zero :
    (∑ x ∈ Finset.range 47,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (161 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (161 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_161 :
    recurrence2Scalar1Left.coeff 161 =
      -(((57341770361257862766199781608213590749193822376 * 10 ^ 70 +
        7417785937360664331335934463865782600298942674811631205821905027634143) * 10 ^ 70 +
        9636974201949079251628236560701008233564901526569385986950789953741639) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 162 = 47 +
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
  rw [recurrence2Scalar1Left_coeff_161_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_162_prefix_zero :
    (∑ x ∈ Finset.range 48,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (162 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (162 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_162 :
    recurrence2Scalar1Left.coeff 162 =
      (((78440864589606378228440756293921587889785745492 * 10 ^ 70 +
        3710913159091691466517948591680022768436228028277271279905050828664123) * 10 ^ 70 +
        1164641813743434288029708642993726489350888745962325939971791997657403) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 163 = 48 +
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
  rw [recurrence2Scalar1Left_coeff_162_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_163_prefix_zero :
    (∑ x ∈ Finset.range 49,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (163 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (163 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_163 :
    recurrence2Scalar1Left.coeff 163 =
      (((351182212514311385194474739527360198264778178911 * 10 ^ 70 +
        0048008428008543543233658746123556652627516362746510319731799103803745) * 10 ^ 70 +
        0881386803155492769418372487651351596786983970906163997693424569366407) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 164 = 49 +
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
  rw [recurrence2Scalar1Left_coeff_163_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_164_prefix_zero :
    (∑ x ∈ Finset.range 50,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (164 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (164 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_164 :
    recurrence2Scalar1Left.coeff 164 =
      -(((2238867529449222886539011144110206664665004686713 * 10 ^ 70 +
        9191926306296552751078176910037287249150348262607415989652561248724705) * 10 ^ 70 +
        0923543060551434764306577177075404695868203102186540858023136307813254) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 165 = 50 +
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
  rw [recurrence2Scalar1Left_coeff_164_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_165_prefix_zero :
    (∑ x ∈ Finset.range 51,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (165 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (165 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_165 :
    recurrence2Scalar1Left.coeff 165 =
      (((4818005143432084743625589909215474051659151200472 * 10 ^ 70 +
        7588145030192998046415656571546831083657143422749047256871037161534695) * 10 ^ 70 +
        2144116896058516358557050088296349655560268197249990270000332476028342) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 166 = 51 +
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
  rw [recurrence2Scalar1Left_coeff_165_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_166_prefix_zero :
    (∑ x ∈ Finset.range 52,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (166 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (166 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_166 :
    recurrence2Scalar1Left.coeff 166 =
      (((5313020058310928035767136107409925130246638495881 * 10 ^ 70 +
        8372638748568522264031126332988326644503196405822870834393501899591654) * 10 ^ 70 +
        3196602352145708477212569662551115333168049009764242529777980290391813) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 167 = 52 +
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
  rw [recurrence2Scalar1Left_coeff_166_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_167_prefix_zero :
    (∑ x ∈ Finset.range 53,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (167 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (167 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_167 :
    recurrence2Scalar1Left.coeff 167 =
      -(((70352432812767977215251378082023850570161722467236 * 10 ^ 70 +
        6133121760968913683222243049937813874582325033293843329715833010027740) * 10 ^ 70 +
        5873529809480673411491548329527984540290629279703070274990364987376953) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 168 = 53 +
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
  rw [recurrence2Scalar1Left_coeff_167_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_168_prefix_zero :
    (∑ x ∈ Finset.range 54,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (168 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (168 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_168 :
    recurrence2Scalar1Left.coeff 168 =
      (((212705662561740215877276523180085609695961585585373 * 10 ^ 70 +
        4649107947818129235085324691514572836403445405113591102943632464153429) * 10 ^ 70 +
        7814302447245323637399317297674501359276537205432770115458429391261787) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 169 = 54 +
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
  rw [recurrence2Scalar1Left_coeff_168_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_169_prefix_zero :
    (∑ x ∈ Finset.range 55,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (169 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (169 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_169 :
    recurrence2Scalar1Left.coeff 169 =
      -(((98784486397810614303877112309493465608037010352768 * 10 ^ 70 +
        2736595293553341780238359782865828851041502722507681700329508910726774) * 10 ^ 70 +
        6537352488243837335771014342798498063244304767835849794782207116723151) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 170 = 55 +
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
  rw [recurrence2Scalar1Left_coeff_169_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_170_prefix_zero :
    (∑ x ∈ Finset.range 56,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (170 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (170 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_170 :
    recurrence2Scalar1Left.coeff 170 =
      -(((1726976465038031450723123548307209120709674417486350 * 10 ^ 70 +
        0583522064638399232421823204173539871895707504125571213135899409454140) * 10 ^ 70 +
        6985290455129985913451234190410001570507222406173083346123014544357408) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 171 = 56 +
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
  rw [recurrence2Scalar1Left_coeff_170_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_171_prefix_zero :
    (∑ x ∈ Finset.range 57,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (171 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (171 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_171 :
    recurrence2Scalar1Left.coeff 171 =
      (((7471706993208087036697715549152727840601222778059216 * 10 ^ 70 +
        3910655783553118929511897844275599863974917692738047736538374057246823) * 10 ^ 70 +
        1233214147078976958759416396579541000555483756423448364128662936206284) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 172 = 57 +
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
  rw [recurrence2Scalar1Left_coeff_171_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_172_prefix_zero :
    (∑ x ∈ Finset.range 58,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (172 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (172 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_172 :
    recurrence2Scalar1Left.coeff 172 =
      -(((11598505754996078272925804581532852191180258575100609 * 10 ^ 70 +
        5404922749435973786803360204696593528415790154912167458598270728452463) * 10 ^ 70 +
        8509141052899927819175207420869289992177508059300412404408405696318225) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 173 = 58 +
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
  rw [recurrence2Scalar1Left_coeff_172_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_173_prefix_zero :
    (∑ x ∈ Finset.range 59,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (173 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (173 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_173 :
    recurrence2Scalar1Left.coeff 173 =
      -(((27031955744644789153632798851229023180415461498974644 * 10 ^ 70 +
        8973568289951753915513236686815564026027536902756904080021200354414298) * 10 ^ 70 +
        5141770476208591456219662516519223846267751568118546357462817813131629) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 174 = 59 +
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
  rw [recurrence2Scalar1Left_coeff_173_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_174_prefix_zero :
    (∑ x ∈ Finset.range 60,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (174 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (174 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_174 :
    recurrence2Scalar1Left.coeff 174 =
      (((211155297799683640884147505965414073754741129880673374 * 10 ^ 70 +
        1485096734250436090871255398405411270492541948015461192932066480964211) * 10 ^ 70 +
        2812540533442130769809117441622681954926207828742691191010584503745879) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 175 = 60 +
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
  rw [recurrence2Scalar1Left_coeff_174_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_175_prefix_zero :
    (∑ x ∈ Finset.range 61,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (175 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (175 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_175 :
    recurrence2Scalar1Left.coeff 175 =
      -(((553619258051833272751899371111120509973774765172347900 * 10 ^ 70 +
        7968896683953490334830350468972925502835060161747155062592878712787427) * 10 ^ 70 +
        4976219973426058619809841979927893213860242160573064093923627807481632) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 176 = 61 +
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
  rw [recurrence2Scalar1Left_coeff_175_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_176_prefix_zero :
    (∑ x ∈ Finset.range 62,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (176 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (176 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_176 :
    recurrence2Scalar1Left.coeff 176 =
      (((189366444459218339938018135752120175780719198014480444 * 10 ^ 70 +
        5327730288257602198031538644722970491134317793622217993768327628686303) * 10 ^ 70 +
        8349647519372698032608351930671056891971518034938306738962401520493395) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 177 = 62 +
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
  rw [recurrence2Scalar1Left_coeff_176_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_177_prefix_zero :
    (∑ x ∈ Finset.range 63,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (177 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (177 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_177 :
    recurrence2Scalar1Left.coeff 177 =
      (((4246607073861641298219466616841283998969734604809597489 * 10 ^ 70 +
        9394478431872831408153462747525509584273461396528845507433545487362225) * 10 ^ 70 +
        2274887844312974942660682556907217098911973965040401773234718928338811) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 178 = 63 +
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
  rw [recurrence2Scalar1Left_coeff_177_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_178_prefix_zero :
    (∑ x ∈ Finset.range 64,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (178 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (178 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_178 :
    recurrence2Scalar1Left.coeff 178 =
      -(((17996337963904997698528298496482538870349295547531740837 * 10 ^ 70 +
        0051147353911203804723514109160507270813818778812250255944613084593685) * 10 ^ 70 +
        1058725016431089023952763767431491184420487876347722939201785511304749) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 179 = 64 +
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
  rw [recurrence2Scalar1Left_coeff_178_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_179_prefix_zero :
    (∑ x ∈ Finset.range 65,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (179 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (179 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_179 :
    recurrence2Scalar1Left.coeff 179 =
      (((32421302778106321162915786715362414775299480104112455610 * 10 ^ 70 +
        1997604797837404183293946857116698806811003633389526209484910945545031) * 10 ^ 70 +
        9156028179753974698143105158123171973900997878331995662258517129644202) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 180 = 65 +
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
  rw [recurrence2Scalar1Left_coeff_179_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_180_prefix_zero :
    (∑ x ∈ Finset.range 66,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (180 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (180 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_180 :
    recurrence2Scalar1Left.coeff 180 =
      (((28600538568494755590373031140775705482131322616007655615 * 10 ^ 70 +
        0863571127217549823256056669023307764030966584735368624645348728485296) * 10 ^ 70 +
        5225057913703116838018103696496657651765517779182017855693694714097875) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 181 = 66 +
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
  rw [recurrence2Scalar1Left_coeff_180_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_181_prefix_zero :
    (∑ x ∈ Finset.range 67,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (181 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (181 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_181 :
    recurrence2Scalar1Left.coeff 181 =
      -(((382579151696174486219208148688236269021759647039006728731 * 10 ^ 70 +
        9058645718039466657281942734426487924004185139941564313090882099941834) * 10 ^ 70 +
        9053145696025389182273457372631194627741628017782920688329841577573445) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 182 = 67 +
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
  rw [recurrence2Scalar1Left_coeff_181_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_182_prefix_zero :
    (∑ x ∈ Finset.range 68,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (182 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (182 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_182 :
    recurrence2Scalar1Left.coeff 182 =
      (((1243917066731898455049958741343439877711956748221409491777 * 10 ^ 70 +
        9825691220424830907809684884405345511275427605535851713412797414291770) * 10 ^ 70 +
        7469476217380312259472975237680855140236158753543706109988938622491443) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 183 = 68 +
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
  rw [recurrence2Scalar1Left_coeff_182_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_183_prefix_zero :
    (∑ x ∈ Finset.range 69,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (183 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (183 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_183 :
    recurrence2Scalar1Left.coeff 183 =
      -(((1717053111808679803322874170877488161817421099885737897151 * 10 ^ 70 +
        7608117177620822720690558893205778619646213114217380745106096691786242) * 10 ^ 70 +
        4675313867674983857747091020410278680164103197138763416187698062136246) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 184 = 69 +
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
  rw [recurrence2Scalar1Left_coeff_183_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_184_prefix_zero :
    (∑ x ∈ Finset.range 70,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (184 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (184 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_184 :
    recurrence2Scalar1Left.coeff 184 =
      -(((3240693682060716306664439127492514935843338284085842098032 * 10 ^ 70 +
        1738820301762707299905955548219763759756151830263175669039827840556596) * 10 ^ 70 +
        5071721462616139189251731965878929849952924521148316528687448579372158) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 185 = 70 +
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
  rw [recurrence2Scalar1Left_coeff_184_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_185_prefix_zero :
    (∑ x ∈ Finset.range 71,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (185 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (185 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_185 :
    recurrence2Scalar1Left.coeff 185 =
      (((25951896717950121597458827779500576402397225167201068197188 * 10 ^ 70 +
        0583746294635132310939579315170079925784633029921063240499727796948612) * 10 ^ 70 +
        6991336759771536390246531276113499014089650656779589660923311452580709) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 186 = 71 +
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
  rw [recurrence2Scalar1Left_coeff_185_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_186_prefix_zero :
    (∑ x ∈ Finset.range 72,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (186 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (186 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_186 :
    recurrence2Scalar1Left.coeff 186 =
      -(((75642194237127787638837120490795471146539582452971690357823 * 10 ^ 70 +
        4617303903009975078314859349838760769370204763529903410967405616176005) * 10 ^ 70 +
        0931720502773601912530894375782974781106710548510483614604161629892373) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 187 = 72 +
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
  rw [recurrence2Scalar1Left_coeff_186_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_187_prefix_zero :
    (∑ x ∈ Finset.range 73,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (187 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (187 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_187 :
    recurrence2Scalar1Left.coeff 187 =
      (((97407497985861939567199574714384591019499200866586076499415 * 10 ^ 70 +
        1909716079055525426632408380494235915907332943673790042196323920591906) * 10 ^ 70 +
        5536043808237834485404032716850027337122632434905559430346562537938765) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 188 = 73 +
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
  rw [recurrence2Scalar1Left_coeff_187_prefix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence2Scalar1Left_coeff_188_prefix_zero :
    (∑ x ∈ Finset.range 74,
      recurrence2LeadingSquare.coeff x * remainder2Coefficient1.coeff (188 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [recurrence2A1_coeff_high (188 - x) (by
    simp only [Finset.mem_range] at hx
    omega)]
  norm_num

theorem recurrence2Scalar1Left_coeff_188 :
    recurrence2Scalar1Left.coeff 188 =
      (((182894997702681246640615346065576464877181307788793677338366 * 10 ^ 70 +
        1300400645780445795737061980381103517057058084292450889046500162435839) * 10 ^ 70 +
        1681951424529895848692082239873888271159083126543096431932885761896320) : ℚ) := by
  unfold recurrence2Scalar1Left
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num only [Nat.succ_eq_add_one]
  rw [show 189 = 74 +
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
  rw [recurrence2Scalar1Left_coeff_188_prefix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
