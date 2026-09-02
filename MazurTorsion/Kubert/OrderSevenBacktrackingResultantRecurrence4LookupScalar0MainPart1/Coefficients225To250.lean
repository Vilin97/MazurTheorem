/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
module
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupDefinitions
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupB0
public import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupQuotientConstant
import MazurTorsion.Kubert.OrderSevenBacktrackingResultantRecurrence4LookupScalar0MainPart1Simp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Recurrence 4 lookup certificate: Scalar0Main coefficient convolution

This is a checked coefficient-lookup shard for the fourth
pseudo-division recurrence in the order-seven certificate.
-/
public section
open Polynomial

namespace MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
namespace Internal.ResultantCertificate

noncomputable section

attribute [local simp]
  recurrence4B0_coeff_1
  recurrence4B0_coeff_10
  recurrence4B0_coeff_100
  recurrence4B0_coeff_101
  recurrence4B0_coeff_102
  recurrence4B0_coeff_103
  recurrence4B0_coeff_104
  recurrence4B0_coeff_105
  recurrence4B0_coeff_106
  recurrence4B0_coeff_107
  recurrence4B0_coeff_108
  recurrence4B0_coeff_109
  recurrence4B0_coeff_11
  recurrence4B0_coeff_110
  recurrence4B0_coeff_111
  recurrence4B0_coeff_112
  recurrence4B0_coeff_113
  recurrence4B0_coeff_114
  recurrence4B0_coeff_115
  recurrence4B0_coeff_116
  recurrence4B0_coeff_117
  recurrence4B0_coeff_118
  recurrence4B0_coeff_119
  recurrence4B0_coeff_12
  recurrence4B0_coeff_120
  recurrence4B0_coeff_121
  recurrence4B0_coeff_122
  recurrence4B0_coeff_123
  recurrence4B0_coeff_124
  recurrence4B0_coeff_125
  recurrence4B0_coeff_126
  recurrence4B0_coeff_127
  recurrence4B0_coeff_128
  recurrence4B0_coeff_129
  recurrence4B0_coeff_13
  recurrence4B0_coeff_130
  recurrence4B0_coeff_131
  recurrence4B0_coeff_132
  recurrence4B0_coeff_133
  recurrence4B0_coeff_134
  recurrence4B0_coeff_135
  recurrence4B0_coeff_136
  recurrence4B0_coeff_137
  recurrence4B0_coeff_138
  recurrence4B0_coeff_139
  recurrence4B0_coeff_14
  recurrence4B0_coeff_140
  recurrence4B0_coeff_141
  recurrence4B0_coeff_142
  recurrence4B0_coeff_143
  recurrence4B0_coeff_144
  recurrence4B0_coeff_145
  recurrence4B0_coeff_146
  recurrence4B0_coeff_147
  recurrence4B0_coeff_148
  recurrence4B0_coeff_149
  recurrence4B0_coeff_15
  recurrence4B0_coeff_150
  recurrence4B0_coeff_151
  recurrence4B0_coeff_152
  recurrence4B0_coeff_153
  recurrence4B0_coeff_154
  recurrence4B0_coeff_155
  recurrence4B0_coeff_156

attribute [local simp]
  recurrence4B0_coeff_157
  recurrence4B0_coeff_158
  recurrence4B0_coeff_159
  recurrence4B0_coeff_16
  recurrence4B0_coeff_160
  recurrence4B0_coeff_161
  recurrence4B0_coeff_162
  recurrence4B0_coeff_163
  recurrence4B0_coeff_164
  recurrence4B0_coeff_165
  recurrence4B0_coeff_166
  recurrence4B0_coeff_167
  recurrence4B0_coeff_168
  recurrence4B0_coeff_169
  recurrence4B0_coeff_17
  recurrence4B0_coeff_170
  recurrence4B0_coeff_171
  recurrence4B0_coeff_172
  recurrence4B0_coeff_173
  recurrence4B0_coeff_174
  recurrence4B0_coeff_175
  recurrence4B0_coeff_176
  recurrence4B0_coeff_18
  recurrence4B0_coeff_19
  recurrence4B0_coeff_2
  recurrence4B0_coeff_20
  recurrence4B0_coeff_21
  recurrence4B0_coeff_22
  recurrence4B0_coeff_23
  recurrence4B0_coeff_24
  recurrence4B0_coeff_25
  recurrence4B0_coeff_26
  recurrence4B0_coeff_27
  recurrence4B0_coeff_28
  recurrence4B0_coeff_29
  recurrence4B0_coeff_3
  recurrence4B0_coeff_30
  recurrence4B0_coeff_31
  recurrence4B0_coeff_32
  recurrence4B0_coeff_33
  recurrence4B0_coeff_34
  recurrence4B0_coeff_35
  recurrence4B0_coeff_36
  recurrence4B0_coeff_37
  recurrence4B0_coeff_38
  recurrence4B0_coeff_39
  recurrence4B0_coeff_4
  recurrence4B0_coeff_40
  recurrence4B0_coeff_41
  recurrence4B0_coeff_42
  recurrence4B0_coeff_43
  recurrence4B0_coeff_44
  recurrence4B0_coeff_45
  recurrence4B0_coeff_46
  recurrence4B0_coeff_47
  recurrence4B0_coeff_48
  recurrence4B0_coeff_49
  recurrence4B0_coeff_5
  recurrence4B0_coeff_50
  recurrence4B0_coeff_51
  recurrence4B0_coeff_52
  recurrence4B0_coeff_53
  recurrence4B0_coeff_54
  recurrence4B0_coeff_55

attribute [local simp]
  recurrence4B0_coeff_56
  recurrence4B0_coeff_57
  recurrence4B0_coeff_58
  recurrence4B0_coeff_59
  recurrence4B0_coeff_6
  recurrence4B0_coeff_60
  recurrence4B0_coeff_61
  recurrence4B0_coeff_62
  recurrence4B0_coeff_63
  recurrence4B0_coeff_64
  recurrence4B0_coeff_65
  recurrence4B0_coeff_66
  recurrence4B0_coeff_67
  recurrence4B0_coeff_68
  recurrence4B0_coeff_69
  recurrence4B0_coeff_7
  recurrence4B0_coeff_70
  recurrence4B0_coeff_71
  recurrence4B0_coeff_72
  recurrence4B0_coeff_73
  recurrence4B0_coeff_74
  recurrence4B0_coeff_75
  recurrence4B0_coeff_76
  recurrence4B0_coeff_77
  recurrence4B0_coeff_78
  recurrence4B0_coeff_79
  recurrence4B0_coeff_8
  recurrence4B0_coeff_80
  recurrence4B0_coeff_81
  recurrence4B0_coeff_82
  recurrence4B0_coeff_83
  recurrence4B0_coeff_84
  recurrence4B0_coeff_85
  recurrence4B0_coeff_86
  recurrence4B0_coeff_87
  recurrence4B0_coeff_88
  recurrence4B0_coeff_89
  recurrence4B0_coeff_9
  recurrence4B0_coeff_90
  recurrence4B0_coeff_91
  recurrence4B0_coeff_92
  recurrence4B0_coeff_93
  recurrence4B0_coeff_94
  recurrence4B0_coeff_95
  recurrence4B0_coeff_96
  recurrence4B0_coeff_97
  recurrence4B0_coeff_98
  recurrence4B0_coeff_99
  recurrence4QuotientConstant_coeff_0
  recurrence4QuotientConstant_coeff_1
  recurrence4QuotientConstant_coeff_10
  recurrence4QuotientConstant_coeff_100
  recurrence4QuotientConstant_coeff_101
  recurrence4QuotientConstant_coeff_102
  recurrence4QuotientConstant_coeff_103
  recurrence4QuotientConstant_coeff_104
  recurrence4QuotientConstant_coeff_105
  recurrence4QuotientConstant_coeff_106
  recurrence4QuotientConstant_coeff_107
  recurrence4QuotientConstant_coeff_108
  recurrence4QuotientConstant_coeff_109
  recurrence4QuotientConstant_coeff_11
  recurrence4QuotientConstant_coeff_110
  recurrence4QuotientConstant_coeff_111

attribute [local simp]
  recurrence4QuotientConstant_coeff_112
  recurrence4QuotientConstant_coeff_113
  recurrence4QuotientConstant_coeff_114
  recurrence4QuotientConstant_coeff_115
  recurrence4QuotientConstant_coeff_116
  recurrence4QuotientConstant_coeff_117
  recurrence4QuotientConstant_coeff_118
  recurrence4QuotientConstant_coeff_119
  recurrence4QuotientConstant_coeff_12
  recurrence4QuotientConstant_coeff_120
  recurrence4QuotientConstant_coeff_121
  recurrence4QuotientConstant_coeff_122
  recurrence4QuotientConstant_coeff_123
  recurrence4QuotientConstant_coeff_124
  recurrence4QuotientConstant_coeff_125
  recurrence4QuotientConstant_coeff_126
  recurrence4QuotientConstant_coeff_127
  recurrence4QuotientConstant_coeff_128
  recurrence4QuotientConstant_coeff_129
  recurrence4QuotientConstant_coeff_13
  recurrence4QuotientConstant_coeff_130
  recurrence4QuotientConstant_coeff_131
  recurrence4QuotientConstant_coeff_132
  recurrence4QuotientConstant_coeff_133
  recurrence4QuotientConstant_coeff_134
  recurrence4QuotientConstant_coeff_135
  recurrence4QuotientConstant_coeff_136
  recurrence4QuotientConstant_coeff_137
  recurrence4QuotientConstant_coeff_138
  recurrence4QuotientConstant_coeff_139
  recurrence4QuotientConstant_coeff_14
  recurrence4QuotientConstant_coeff_140
  recurrence4QuotientConstant_coeff_141
  recurrence4QuotientConstant_coeff_142
  recurrence4QuotientConstant_coeff_143
  recurrence4QuotientConstant_coeff_144
  recurrence4QuotientConstant_coeff_145
  recurrence4QuotientConstant_coeff_146
  recurrence4QuotientConstant_coeff_147
  recurrence4QuotientConstant_coeff_148
  recurrence4QuotientConstant_coeff_149
  recurrence4QuotientConstant_coeff_15
  recurrence4QuotientConstant_coeff_150
  recurrence4QuotientConstant_coeff_151
  recurrence4QuotientConstant_coeff_152
  recurrence4QuotientConstant_coeff_153
  recurrence4QuotientConstant_coeff_154
  recurrence4QuotientConstant_coeff_155
  recurrence4QuotientConstant_coeff_156
  recurrence4QuotientConstant_coeff_157
  recurrence4QuotientConstant_coeff_158
  recurrence4QuotientConstant_coeff_159
  recurrence4QuotientConstant_coeff_16
  recurrence4QuotientConstant_coeff_160
  recurrence4QuotientConstant_coeff_161
  recurrence4QuotientConstant_coeff_162
  recurrence4QuotientConstant_coeff_163
  recurrence4QuotientConstant_coeff_164
  recurrence4QuotientConstant_coeff_165
  recurrence4QuotientConstant_coeff_166
  recurrence4QuotientConstant_coeff_167
  recurrence4QuotientConstant_coeff_168
  recurrence4QuotientConstant_coeff_169
  recurrence4QuotientConstant_coeff_17

attribute [local simp]
  recurrence4QuotientConstant_coeff_170
  recurrence4QuotientConstant_coeff_171
  recurrence4QuotientConstant_coeff_172
  recurrence4QuotientConstant_coeff_173
  recurrence4QuotientConstant_coeff_174
  recurrence4QuotientConstant_coeff_175
  recurrence4QuotientConstant_coeff_176
  recurrence4QuotientConstant_coeff_177
  recurrence4QuotientConstant_coeff_178
  recurrence4QuotientConstant_coeff_179
  recurrence4QuotientConstant_coeff_18
  recurrence4QuotientConstant_coeff_180
  recurrence4QuotientConstant_coeff_181
  recurrence4QuotientConstant_coeff_182
  recurrence4QuotientConstant_coeff_183
  recurrence4QuotientConstant_coeff_184
  recurrence4QuotientConstant_coeff_185
  recurrence4QuotientConstant_coeff_186
  recurrence4QuotientConstant_coeff_187
  recurrence4QuotientConstant_coeff_188
  recurrence4QuotientConstant_coeff_189
  recurrence4QuotientConstant_coeff_19
  recurrence4QuotientConstant_coeff_190
  recurrence4QuotientConstant_coeff_191
  recurrence4QuotientConstant_coeff_192
  recurrence4QuotientConstant_coeff_193
  recurrence4QuotientConstant_coeff_194
  recurrence4QuotientConstant_coeff_195
  recurrence4QuotientConstant_coeff_196
  recurrence4QuotientConstant_coeff_197
  recurrence4QuotientConstant_coeff_198
  recurrence4QuotientConstant_coeff_199
  recurrence4QuotientConstant_coeff_2
  recurrence4QuotientConstant_coeff_20
  recurrence4QuotientConstant_coeff_200
  recurrence4QuotientConstant_coeff_201
  recurrence4QuotientConstant_coeff_202
  recurrence4QuotientConstant_coeff_203
  recurrence4QuotientConstant_coeff_204
  recurrence4QuotientConstant_coeff_205
  recurrence4QuotientConstant_coeff_206
  recurrence4QuotientConstant_coeff_207
  recurrence4QuotientConstant_coeff_208
  recurrence4QuotientConstant_coeff_209
  recurrence4QuotientConstant_coeff_21
  recurrence4QuotientConstant_coeff_210
  recurrence4QuotientConstant_coeff_211
  recurrence4QuotientConstant_coeff_212
  recurrence4QuotientConstant_coeff_213
  recurrence4QuotientConstant_coeff_214
  recurrence4QuotientConstant_coeff_215
  recurrence4QuotientConstant_coeff_216
  recurrence4QuotientConstant_coeff_217
  recurrence4QuotientConstant_coeff_218
  recurrence4QuotientConstant_coeff_219
  recurrence4QuotientConstant_coeff_22
  recurrence4QuotientConstant_coeff_220
  recurrence4QuotientConstant_coeff_221
  recurrence4QuotientConstant_coeff_222
  recurrence4QuotientConstant_coeff_223
  recurrence4QuotientConstant_coeff_224
  recurrence4QuotientConstant_coeff_225
  recurrence4QuotientConstant_coeff_226
  recurrence4QuotientConstant_coeff_227

attribute [local simp]
  recurrence4QuotientConstant_coeff_228
  recurrence4QuotientConstant_coeff_229
  recurrence4QuotientConstant_coeff_23
  recurrence4QuotientConstant_coeff_230
  recurrence4QuotientConstant_coeff_231
  recurrence4QuotientConstant_coeff_232
  recurrence4QuotientConstant_coeff_233
  recurrence4QuotientConstant_coeff_234
  recurrence4QuotientConstant_coeff_235
  recurrence4QuotientConstant_coeff_236
  recurrence4QuotientConstant_coeff_237
  recurrence4QuotientConstant_coeff_238
  recurrence4QuotientConstant_coeff_239
  recurrence4QuotientConstant_coeff_24
  recurrence4QuotientConstant_coeff_240
  recurrence4QuotientConstant_coeff_241
  recurrence4QuotientConstant_coeff_242
  recurrence4QuotientConstant_coeff_243
  recurrence4QuotientConstant_coeff_244
  recurrence4QuotientConstant_coeff_245
  recurrence4QuotientConstant_coeff_246
  recurrence4QuotientConstant_coeff_247
  recurrence4QuotientConstant_coeff_248
  recurrence4QuotientConstant_coeff_249
  recurrence4QuotientConstant_coeff_25
  recurrence4QuotientConstant_coeff_250
  recurrence4QuotientConstant_coeff_251
  recurrence4QuotientConstant_coeff_252
  recurrence4QuotientConstant_coeff_253
  recurrence4QuotientConstant_coeff_254
  recurrence4QuotientConstant_coeff_255
  recurrence4QuotientConstant_coeff_256
  recurrence4QuotientConstant_coeff_257
  recurrence4QuotientConstant_coeff_258
  recurrence4QuotientConstant_coeff_259
  recurrence4QuotientConstant_coeff_26
  recurrence4QuotientConstant_coeff_260
  recurrence4QuotientConstant_coeff_261
  recurrence4QuotientConstant_coeff_262
  recurrence4QuotientConstant_coeff_263
  recurrence4QuotientConstant_coeff_264
  recurrence4QuotientConstant_coeff_265
  recurrence4QuotientConstant_coeff_266
  recurrence4QuotientConstant_coeff_267
  recurrence4QuotientConstant_coeff_268
  recurrence4QuotientConstant_coeff_269
  recurrence4QuotientConstant_coeff_27
  recurrence4QuotientConstant_coeff_270
  recurrence4QuotientConstant_coeff_271
  recurrence4QuotientConstant_coeff_272
  recurrence4QuotientConstant_coeff_273
  recurrence4QuotientConstant_coeff_274
  recurrence4QuotientConstant_coeff_275
  recurrence4QuotientConstant_coeff_28
  recurrence4QuotientConstant_coeff_29
  recurrence4QuotientConstant_coeff_3
  recurrence4QuotientConstant_coeff_30
  recurrence4QuotientConstant_coeff_31
  recurrence4QuotientConstant_coeff_32
  recurrence4QuotientConstant_coeff_33
  recurrence4QuotientConstant_coeff_34
  recurrence4QuotientConstant_coeff_35
  recurrence4QuotientConstant_coeff_36
  recurrence4QuotientConstant_coeff_37

attribute [local simp]
  recurrence4QuotientConstant_coeff_38
  recurrence4QuotientConstant_coeff_39
  recurrence4QuotientConstant_coeff_4
  recurrence4QuotientConstant_coeff_40
  recurrence4QuotientConstant_coeff_41
  recurrence4QuotientConstant_coeff_42
  recurrence4QuotientConstant_coeff_43
  recurrence4QuotientConstant_coeff_44
  recurrence4QuotientConstant_coeff_45
  recurrence4QuotientConstant_coeff_46
  recurrence4QuotientConstant_coeff_47
  recurrence4QuotientConstant_coeff_48
  recurrence4QuotientConstant_coeff_49
  recurrence4QuotientConstant_coeff_5
  recurrence4QuotientConstant_coeff_50
  recurrence4QuotientConstant_coeff_51
  recurrence4QuotientConstant_coeff_52
  recurrence4QuotientConstant_coeff_53
  recurrence4QuotientConstant_coeff_54
  recurrence4QuotientConstant_coeff_55
  recurrence4QuotientConstant_coeff_56
  recurrence4QuotientConstant_coeff_57
  recurrence4QuotientConstant_coeff_58
  recurrence4QuotientConstant_coeff_59
  recurrence4QuotientConstant_coeff_6
  recurrence4QuotientConstant_coeff_60
  recurrence4QuotientConstant_coeff_61
  recurrence4QuotientConstant_coeff_62
  recurrence4QuotientConstant_coeff_63
  recurrence4QuotientConstant_coeff_64
  recurrence4QuotientConstant_coeff_65
  recurrence4QuotientConstant_coeff_66
  recurrence4QuotientConstant_coeff_67
  recurrence4QuotientConstant_coeff_68
  recurrence4QuotientConstant_coeff_69
  recurrence4QuotientConstant_coeff_7
  recurrence4QuotientConstant_coeff_70
  recurrence4QuotientConstant_coeff_71
  recurrence4QuotientConstant_coeff_72
  recurrence4QuotientConstant_coeff_73
  recurrence4QuotientConstant_coeff_74
  recurrence4QuotientConstant_coeff_75
  recurrence4QuotientConstant_coeff_76
  recurrence4QuotientConstant_coeff_77
  recurrence4QuotientConstant_coeff_78
  recurrence4QuotientConstant_coeff_79
  recurrence4QuotientConstant_coeff_8
  recurrence4QuotientConstant_coeff_80
  recurrence4QuotientConstant_coeff_81
  recurrence4QuotientConstant_coeff_82
  recurrence4QuotientConstant_coeff_83
  recurrence4QuotientConstant_coeff_84
  recurrence4QuotientConstant_coeff_85
  recurrence4QuotientConstant_coeff_86
  recurrence4QuotientConstant_coeff_87
  recurrence4QuotientConstant_coeff_88
  recurrence4QuotientConstant_coeff_89
  recurrence4QuotientConstant_coeff_9
  recurrence4QuotientConstant_coeff_90
  recurrence4QuotientConstant_coeff_91
  recurrence4QuotientConstant_coeff_92
  recurrence4QuotientConstant_coeff_93
  recurrence4QuotientConstant_coeff_94
  recurrence4QuotientConstant_coeff_95

attribute [local simp]
  recurrence4QuotientConstant_coeff_96
  recurrence4QuotientConstant_coeff_97
  recurrence4QuotientConstant_coeff_98
  recurrence4QuotientConstant_coeff_99

private theorem recurrence4Scalar0Main_coeff_225_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (225 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (225 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_225_suffix_zero :
    (∑ x ∈ Finset.range 49,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (225 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_225 :
    recurrence4Scalar0Main.coeff 225 =
      -(((((140097805114806458355469202 * 10 ^ 70 +
        3385372836537997491965795596973707572746433627514738538060086860375135) * 10 ^ 70 +
        4886882402357810141899590656907064850482012041248839566915583757128426) * 10 ^ 70 +
        7715507916943339376740406880990713755228326923290478808066262898574640) * 10 ^ 70 +
        0650722485249590584678295674740330926161151869206713526978113433989531) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 226,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (225 - x)) = _
  rw [show 226 = 1 +
    225 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 225 = 32 +
      193 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 193 = 32 +
      161 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 161 = 32 +
      129 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 129 = 32 +
      97 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 97 = 32 +
      65 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 65 = 16 +
      49 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_225_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_225_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_226_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (226 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (226 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_226_suffix_zero :
    (∑ x ∈ Finset.range 50,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (226 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_226 :
    recurrence4Scalar0Main.coeff 226 =
      (((((200732559734524803685068694 * 10 ^ 70 +
        4149135063346897559486216107631969167821285562373099710132421296100050) * 10 ^ 70 +
        2021277908921346876707997364927774675942116377362248234336703783270638) * 10 ^ 70 +
        8307982952253656937974937969994344038866345541617911189063533867252632) * 10 ^ 70 +
        5108800412456472550302043527010940831689820328630312329061358730807089) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 227,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (226 - x)) = _
  rw [show 227 = 1 +
    226 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 226 = 32 +
      194 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 194 = 32 +
      162 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 162 = 32 +
      130 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 130 = 32 +
      98 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 98 = 32 +
      66 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 66 = 16 +
      50 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_226_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_226_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_227_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (227 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (227 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_227_suffix_zero :
    (∑ x ∈ Finset.range 51,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (227 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_227 :
    recurrence4Scalar0Main.coeff 227 =
      -(((((283107176512928375988451676 * 10 ^ 70 +
        5203228446242456175471581271088828114486483753873658284081070308751728) * 10 ^ 70 +
        4455562045281244915559597056435928348646287462440419859472544439968479) * 10 ^ 70 +
        6489759866342076013934465868945987801979371793088528316964117380584238) * 10 ^ 70 +
        8191552612380983982954995846117236971886660192504972435255412625609230) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 228,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (227 - x)) = _
  rw [show 228 = 1 +
    227 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 227 = 32 +
      195 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 195 = 32 +
      163 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 163 = 32 +
      131 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 131 = 32 +
      99 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 99 = 32 +
      67 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 67 = 16 +
      51 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_227_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_227_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_228_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (228 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (228 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_228_suffix_zero :
    (∑ x ∈ Finset.range 52,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (228 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_228 :
    recurrence4Scalar0Main.coeff 228 =
      (((((392931714660697324066882935 * 10 ^ 70 +
        0456436729656667462784910264755748813722321818138894640739399684692654) * 10 ^ 70 +
        3713676357276153017101970758242825285596261579849794996200088616741350) * 10 ^ 70 +
        3982048184950267714432860405976980034284019778472680499356916705530402) * 10 ^ 70 +
        7361378838570936030111285621350041475815611780107258143627979595155515) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 229,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (228 - x)) = _
  rw [show 229 = 1 +
    228 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 228 = 32 +
      196 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 196 = 32 +
      164 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 164 = 32 +
      132 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 132 = 32 +
      100 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 100 = 32 +
      68 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 68 = 16 +
      52 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_228_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_228_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_229_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (229 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (229 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_229_suffix_zero :
    (∑ x ∈ Finset.range 53,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (229 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_229 :
    recurrence4Scalar0Main.coeff 229 =
      -(((((536515815879589323963049577 * 10 ^ 70 +
        9091960781952156054330086653991352177764759065391087182053102909953505) * 10 ^ 70 +
        4613319811921442343064428175391082438741818729406302507559042354390350) * 10 ^ 70 +
        0115763312927694541057475723978084511667961909053668602619951182340555) * 10 ^ 70 +
        0147979983537679719700382660810417986779200773827454662594964425288297) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 230,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (229 - x)) = _
  rw [show 230 = 1 +
    229 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 229 = 32 +
      197 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 197 = 32 +
      165 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 165 = 32 +
      133 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 133 = 32 +
      101 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 101 = 32 +
      69 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 69 = 16 +
      53 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_229_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_229_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_230_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (230 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (230 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_230_suffix_zero :
    (∑ x ∈ Finset.range 54,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (230 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_230 :
    recurrence4Scalar0Main.coeff 230 =
      (((((720423521989912734934058858 * 10 ^ 70 +
        1795727384686597425824667012253365027971247400326452445908103258058213) * 10 ^ 70 +
        8370912622252690371259707256225675575628972405399835827305957101921377) * 10 ^ 70 +
        3763941193689705258347995983004048739039073061740199312737644429751859) * 10 ^ 70 +
        5329136244520933249097313693115471431944281267039754367108416308900346) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 231,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (230 - x)) = _
  rw [show 231 = 1 +
    230 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 230 = 32 +
      198 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 198 = 32 +
      166 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 166 = 32 +
      134 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 134 = 32 +
      102 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 102 = 32 +
      70 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 70 = 16 +
      54 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_230_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_230_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_231_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (231 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (231 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_231_suffix_zero :
    (∑ x ∈ Finset.range 55,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (231 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_231 :
    recurrence4Scalar0Main.coeff 231 =
      -(((((950915372675416542635250040 * 10 ^ 70 +
        8356700885356546587526265428785367663418625984790582287647954696853821) * 10 ^ 70 +
        1306280453540272328247019726669887202055510308874763107233841164220975) * 10 ^ 70 +
        8486111555588365616933985483013530449648970199841789535790849709189682) * 10 ^ 70 +
        0561048960407905590907816673599480104999745164033909290740129739108036) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 232,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (231 - x)) = _
  rw [show 232 = 1 +
    231 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 231 = 32 +
      199 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 199 = 32 +
      167 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 167 = 32 +
      135 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 135 = 32 +
      103 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 103 = 32 +
      71 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 71 = 16 +
      55 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_231_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_231_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_232_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (232 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (232 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_232_suffix_zero :
    (∑ x ∈ Finset.range 56,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (232 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_232 :
    recurrence4Scalar0Main.coeff 232 =
      (((((1233140220133989119002057795 * 10 ^ 70 +
        4119306064860100819465212037465508470081493533700585432207149549155069) * 10 ^ 70 +
        7804449880305015748374012441533737411276159413019674574251815821565847) * 10 ^ 70 +
        8833749967114345857984946290210410673408965838057721149948650842433470) * 10 ^ 70 +
        2818098698743626407572222814154521546880241799134165155099002511375877) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 233,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (232 - x)) = _
  rw [show 233 = 1 +
    232 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 232 = 32 +
      200 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 200 = 32 +
      168 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 168 = 32 +
      136 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 136 = 32 +
      104 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 104 = 32 +
      72 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 72 = 16 +
      56 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_232_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_232_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_233_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (233 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (233 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_233_suffix_zero :
    (∑ x ∈ Finset.range 57,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (233 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_233 :
    recurrence4Scalar0Main.coeff 233 =
      -(((((1570054948954223646715648813 * 10 ^ 70 +
        0782337612150866440212900165063091830315747974004949845605668933190570) * 10 ^ 70 +
        8010977397768913509716422702094718236263276183343752054963232050485556) * 10 ^ 70 +
        7717345944170361038287553390818501723498531942617042130156985958128567) * 10 ^ 70 +
        7705632605524098504117547919115679673661411058420975184902026792842164) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 234,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (233 - x)) = _
  rw [show 234 = 1 +
    233 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 233 = 32 +
      201 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 201 = 32 +
      169 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 169 = 32 +
      137 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 137 = 32 +
      105 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 105 = 32 +
      73 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 73 = 16 +
      57 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_233_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_233_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_234_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (234 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (234 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_234_suffix_zero :
    (∑ x ∈ Finset.range 58,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (234 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_234 :
    recurrence4Scalar0Main.coeff 234 =
      (((((1961076403263019081393583265 * 10 ^ 70 +
        8994781590254016014325759175229608927971006044844003580983707867250256) * 10 ^ 70 +
        6355373335491911386758380557791461088035674783037897199746734238031097) * 10 ^ 70 +
        1948494556926186419187622861288615210550799276558902864186186531768210) * 10 ^ 70 +
        9186013926665700220636703625232621978032901019240804403696475292246142) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 235,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (234 - x)) = _
  rw [show 235 = 1 +
    234 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 234 = 32 +
      202 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 202 = 32 +
      170 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 170 = 32 +
      138 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 138 = 32 +
      106 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 106 = 32 +
      74 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 74 = 16 +
      58 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_234_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_234_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_235_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (235 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (235 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_235_suffix_zero :
    (∑ x ∈ Finset.range 59,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (235 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_235 :
    recurrence4Scalar0Main.coeff 235 =
      -(((((2400506673596582658453674769 * 10 ^ 70 +
        0463805546874145345178875635749902685540275408625345247200847870864770) * 10 ^ 70 +
        4519770729750880801018445979700755181044863210821942944962019929048853) * 10 ^ 70 +
        7057606340084973720291541793125713412291237109322606593030614356986402) * 10 ^ 70 +
        5766073654247240964236928999795562966612879030572512437824151612208970) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 236,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (235 - x)) = _
  rw [show 236 = 1 +
    235 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 235 = 32 +
      203 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 203 = 32 +
      171 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 171 = 32 +
      139 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 139 = 32 +
      107 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 107 = 32 +
      75 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 75 = 16 +
      59 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_235_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_235_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_236_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (236 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (236 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_236_suffix_zero :
    (∑ x ∈ Finset.range 60,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (236 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_236 :
    recurrence4Scalar0Main.coeff 236 =
      (((((2875819157709807281428921661 * 10 ^ 70 +
        6758324308268623233326122468149455236324851468269640541917831327272883) * 10 ^ 70 +
        6881750232252837682019933198758590305655820258222306944013147443726088) * 10 ^ 70 +
        3533215556912008766316873170902587534398239227865042447788011207121064) * 10 ^ 70 +
        3234973777367811443677469075054282697159335915179575258889644466783218) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 237,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (236 - x)) = _
  rw [show 237 = 1 +
    236 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 236 = 32 +
      204 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 204 = 32 +
      172 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 172 = 32 +
      140 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 140 = 32 +
      108 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 108 = 32 +
      76 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 76 = 16 +
      60 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_236_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_236_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_237_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (237 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (237 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_237_suffix_zero :
    (∑ x ∈ Finset.range 61,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (237 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_237 :
    recurrence4Scalar0Main.coeff 237 =
      -(((((3365945004846543213295839773 * 10 ^ 70 +
        6601680529618940653439841698886093790807233804634632360360038790273917) * 10 ^ 70 +
        8637453689976884824061397538469688333237999141400381670760043543779412) * 10 ^ 70 +
        1187065319928791214125837093159366657295870063315822026162047418731723) * 10 ^ 70 +
        3706462124542919964587199133164158699684935056073277785777606556177491) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 238,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (237 - x)) = _
  rw [show 238 = 1 +
    237 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 237 = 32 +
      205 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 205 = 32 +
      173 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 173 = 32 +
      141 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 141 = 32 +
      109 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 109 = 32 +
      77 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 77 = 16 +
      61 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_237_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_237_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_238_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (238 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (238 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_238_suffix_zero :
    (∑ x ∈ Finset.range 62,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (238 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_238 :
    recurrence4Scalar0Main.coeff 238 =
      (((((3839751848235163888633406390 * 10 ^ 70 +
        3903720584868259652122261078225603654189560984935053027398858214053093) * 10 ^ 70 +
        6797943423632402191390123276150590132577804466377884372824839963312458) * 10 ^ 70 +
        2754827491574037272174447395595221492761961434412984540628855858628285) * 10 ^ 70 +
        0148105140764671354788580894711385745525794040769097483006577845212702) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 239,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (238 - x)) = _
  rw [show 239 = 1 +
    238 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 238 = 32 +
      206 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 206 = 32 +
      174 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 174 = 32 +
      142 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 142 = 32 +
      110 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 110 = 32 +
      78 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 78 = 16 +
      62 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_238_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_238_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_239_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (239 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (239 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_239_suffix_zero :
    (∑ x ∈ Finset.range 63,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (239 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_239 :
    recurrence4Scalar0Main.coeff 239 =
      -(((((4254951122408924917040065357 * 10 ^ 70 +
        5545974086999427416059568275753418535787451908184225729089620409306530) * 10 ^ 70 +
        1426347046920719778000123178590137200837911986381804205343159988240011) * 10 ^ 70 +
        8708024666440508359771172272560991153187334267701502726907396154147982) * 10 ^ 70 +
        0995658312842192386474062033056895510549686850164849789128687741797483) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 240,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (239 - x)) = _
  rw [show 240 = 1 +
    239 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 239 = 32 +
      207 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 207 = 32 +
      175 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 175 = 32 +
      143 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 143 = 32 +
      111 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 111 = 32 +
      79 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 79 = 16 +
      63 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_239_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_239_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_240_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (240 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (240 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_240_suffix_zero :
    (∑ x ∈ Finset.range 64,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (240 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_240 :
    recurrence4Scalar0Main.coeff 240 =
      (((((4557697257390557519003770556 * 10 ^ 70 +
        8334839157253535594553523145850813228619315584277364436861511654189901) * 10 ^ 70 +
        7138946980665257622006354121203354537028673990371371295605396221352597) * 10 ^ 70 +
        5368058469654962335604861309866819702151312484489289807149035356054293) * 10 ^ 70 +
        0154666154002929432461597455475621632374128588501153092048396648649094) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 241,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (240 - x)) = _
  rw [show 241 = 1 +
    240 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 240 = 32 +
      208 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 208 = 32 +
      176 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 176 = 32 +
      144 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 144 = 32 +
      112 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 112 = 32 +
      80 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 80 = 16 +
      64 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_240_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_240_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_241_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (241 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (241 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_241_suffix_zero :
    (∑ x ∈ Finset.range 65,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (241 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_241 :
    recurrence4Scalar0Main.coeff 241 =
      -(((((4683141863502441544112566955 * 10 ^ 70 +
        7595241660436043927848477416042183493955931844774950010484833542727492) * 10 ^ 70 +
        1481237875546321284789781289549374505979697286119597892460053477845281) * 10 ^ 70 +
        9376524820824053443746947036712106362067491565369977312013590087635356) * 10 ^ 70 +
        6193184747283318917016368032946415461731940496555645206232888228006816) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 242,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (241 - x)) = _
  rw [show 242 = 1 +
    241 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 241 = 32 +
      209 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 209 = 32 +
      177 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 177 = 32 +
      145 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 145 = 32 +
      113 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 113 = 32 +
      81 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 81 = 16 +
      65 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_241_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_241_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_242_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (242 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (242 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_242_suffix_zero :
    (∑ x ∈ Finset.range 66,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (242 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_242 :
    recurrence4Scalar0Main.coeff 242 =
      (((((4557170262285831750027954067 * 10 ^ 70 +
        6846793741230076706013834997676448943175666268820903912401397338930283) * 10 ^ 70 +
        3465407693768194725420162593723271901549055787881651289421218599341388) * 10 ^ 70 +
        0624875843242158468540830660034250225313364079659974225099824195161251) * 10 ^ 70 +
        6683468631017731984532911213766293051534337637698439403829108861814896) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 243,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (242 - x)) = _
  rw [show 243 = 1 +
    242 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 242 = 32 +
      210 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 210 = 32 +
      178 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 178 = 32 +
      146 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 146 = 32 +
      114 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 114 = 32 +
      82 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 82 = 16 +
      66 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_242_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_242_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_243_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (243 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (243 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_243_suffix_zero :
    (∑ x ∈ Finset.range 67,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (243 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_243 :
    recurrence4Scalar0Main.coeff 243 =
      -(((((4099471251934925218096505555 * 10 ^ 70 +
        0164250415368836368636891284397703248345915465115319468092143591117174) * 10 ^ 70 +
        8240213650091670174251937739342216261593872778208668923307341178757397) * 10 ^ 70 +
        8655468786063499002625302474166011599891854674420401158731151143821476) * 10 ^ 70 +
        8537521427307331808992366955036564624493472546305527696998917810405849) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 244,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (243 - x)) = _
  rw [show 244 = 1 +
    243 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 243 = 32 +
      211 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 211 = 32 +
      179 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 179 = 32 +
      147 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 147 = 32 +
      115 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 115 = 32 +
      83 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 83 = 16 +
      67 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_243_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_243_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_244_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (244 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (244 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_244_suffix_zero :
    (∑ x ∈ Finset.range 68,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (244 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_244 :
    recurrence4Scalar0Main.coeff 244 =
      (((((3227973810886439310184804158 * 10 ^ 70 +
        4995052074833937480539845072261423572436878600424841679482659640647475) * 10 ^ 70 +
        1206617096090354550972327026964569856813342131045346250939478179704490) * 10 ^ 70 +
        2773422226880694921298282318058615961843847049179017705330406111599640) * 10 ^ 70 +
        2741246805675546467197095941503924596880325125966930256634915833766179) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 245,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (244 - x)) = _
  rw [show 245 = 1 +
    244 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 244 = 32 +
      212 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 212 = 32 +
      180 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 180 = 32 +
      148 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 148 = 32 +
      116 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 116 = 32 +
      84 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 84 = 16 +
      68 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_244_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_244_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_245_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (245 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (245 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_245_suffix_zero :
    (∑ x ∈ Finset.range 69,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (245 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_245 :
    recurrence4Scalar0Main.coeff 245 =
      -(((((1864533037804197387886230220 * 10 ^ 70 +
        7462909865852540049489143663124097697359439101971153035641317157100760) * 10 ^ 70 +
        3407433816681927484576095954287477383335948083580456934282184358418485) * 10 ^ 70 +
        7666874010236134563152013047676009189222208163682151575473500615492086) * 10 ^ 70 +
        4783285341016479091069579819570619139032559715594013519705080243950311) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 246,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (245 - x)) = _
  rw [show 246 = 1 +
    245 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 245 = 32 +
      213 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 213 = 32 +
      181 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 181 = 32 +
      149 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 149 = 32 +
      117 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 117 = 32 +
      85 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 85 = 16 +
      69 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_245_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_245_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_246_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (246 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (246 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_246_suffix_zero :
    (∑ x ∈ Finset.range 70,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (246 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_246 :
    recurrence4Scalar0Main.coeff 246 =
      -(((((58424468134759004578128461 * 10 ^ 70 +
        7029731726901060440945060712392355614815709467808463891377767427888542) * 10 ^ 70 +
        7195683948234038446584492424126300165819887586345253242080706968159990) * 10 ^ 70 +
        1014143812847405590950170520816812488147362860725507963343336003267465) * 10 ^ 70 +
        2978796614508444886232965141013706409381213272323921907311563318112425) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 247,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (246 - x)) = _
  rw [show 247 = 1 +
    246 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 246 = 32 +
      214 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 214 = 32 +
      182 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 182 = 32 +
      150 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 150 = 32 +
      118 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 118 = 32 +
      86 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 86 = 16 +
      70 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_246_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_246_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_247_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (247 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (247 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_247_suffix_zero :
    (∑ x ∈ Finset.range 71,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (247 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_247 :
    recurrence4Scalar0Main.coeff 247 =
      (((((2590758448223446627294169559 * 10 ^ 70 +
        3671632993508097040981778023476937503767093843983174691766009425105972) * 10 ^ 70 +
        2900230225838578916104897548841503881523650999900655356662391840341137) * 10 ^ 70 +
        2833619884611493428274664310694054697812454492095099642114344007702615) * 10 ^ 70 +
        1343191221508743014085611952027266093508638443337935695938650571030969) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 248,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (247 - x)) = _
  rw [show 248 = 1 +
    247 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 247 = 32 +
      215 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 215 = 32 +
      183 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 183 = 32 +
      151 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 151 = 32 +
      119 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 119 = 32 +
      87 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 87 = 16 +
      71 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_247_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_247_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_248_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (248 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (248 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_248_suffix_zero :
    (∑ x ∈ Finset.range 72,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (248 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_248 :
    recurrence4Scalar0Main.coeff 248 =
      -(((((5757588013082425598326873354 * 10 ^ 70 +
        0215942138776316726848535388954179983609827544255485907991543500134176) * 10 ^ 70 +
        5490926149302739051601165753547242209554240737948613319063380350230841) * 10 ^ 70 +
        3131388205910870994014603919720026694315862078979767730212093290921133) * 10 ^ 70 +
        7661713667490955445623146490796244254408241064484528638590810984488304) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 249,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (248 - x)) = _
  rw [show 249 = 1 +
    248 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 248 = 32 +
      216 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 216 = 32 +
      184 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 184 = 32 +
      152 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 152 = 32 +
      120 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 120 = 32 +
      88 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 88 = 16 +
      72 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_248_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_248_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_249_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (249 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (249 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_249_suffix_zero :
    (∑ x ∈ Finset.range 73,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (249 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_249 :
    recurrence4Scalar0Main.coeff 249 =
      (((((9553092021058903259202409412 * 10 ^ 70 +
        6632247870150128687919839742711508416312949054776591982782272742398922) * 10 ^ 70 +
        3749104258584417605747792365749130488713020581818311916896383241832043) * 10 ^ 70 +
        1178449448511742207087377229186698557504774455387005457064722738044253) * 10 ^ 70 +
        8080036872222014346031518627720227089584029513148225423904461841496493) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 250,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (249 - x)) = _
  rw [show 250 = 1 +
    249 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 249 = 32 +
      217 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 217 = 32 +
      185 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 185 = 32 +
      153 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 153 = 32 +
      121 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 121 = 32 +
      89 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 89 = 16 +
      73 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_249_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_249_suffix_zero]
  order_seven_normalize_coefficient_sum

private theorem recurrence4Scalar0Main_coeff_250_prefix_zero :
    (∑ x ∈ Finset.range 1,
      remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (250 - x)) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  by_cases hleft : x < 1
  · rw [recurrence4B0_coeff_low x hleft]
    norm_num
  · rw [recurrence4QuotientConstant_coeff_high (250 - x) (by
      omega)]
    norm_num

private theorem recurrence4Scalar0Main_coeff_250_suffix_zero :
    (∑ x ∈ Finset.range 74,
      remainder5Coefficient0.coeff (177 + x) *
        recurrence4QuotientConstant.coeff (250 - (177 + x))) =
      0 := by
  apply Finset.sum_eq_zero
  intro x hx
  simp only [Finset.mem_range] at hx
  rw [recurrence4B0_coeff_high (177 + x) (by
    omega)]
  norm_num

theorem recurrence4Scalar0Main_coeff_250 :
    recurrence4Scalar0Main.coeff 250 =
      -(((((13935877327629295308042696280 * 10 ^ 70 +
        1076926453556179557697547479773277544199213404231177399052240311152539) * 10 ^ 70 +
        2302905656897223371521318989622619958188242004239595523865160277273898) * 10 ^ 70 +
        7820911279010378460069188937036741574052124019110049299295436337847808) * 10 ^ 70 +
        1797780355401107978624061339432919411303849478921014719185758210551761) : ℚ) := by
  unfold recurrence4Scalar0Main
  rw [Polynomial.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  change (∑ x ∈ Finset.range 251,
    remainder5Coefficient0.coeff x * recurrence4QuotientConstant.coeff (250 - x)) = _
  rw [show 251 = 1 +
    250 by norm_num, Finset.sum_range_add]
  conv_lhs =>
    rhs
    rw [show 250 = 32 +
      218 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 218 = 32 +
      186 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 186 = 32 +
      154 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 154 = 32 +
      122 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 122 = 32 +
      90 by norm_num, Finset.sum_range_add]
    rhs
    rw [show 90 = 16 +
      74 by norm_num, Finset.sum_range_add]
  rw [recurrence4Scalar0Main_coeff_250_prefix_zero]
  norm_num only [← Nat.add_assoc]
  rw [recurrence4Scalar0Main_coeff_250_suffix_zero]
  order_seven_normalize_coefficient_sum

end

end Internal.ResultantCertificate
end MazurTorsion.Kubert.OrderSevenBacktrackingCertificate
